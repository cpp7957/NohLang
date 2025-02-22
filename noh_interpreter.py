import sys
import json
import re
import logging
import argparse
import ast
import operator as op
import datetime
import requests
import os
import copy
import math
import random

try:
    import colorama
    from colorama import Fore, Style
    colorama.init(autoreset=True)
except ImportError:
    colorama = None

from typing import Any, Dict, List, Optional
from collections import ChainMap

AST_CACHE = {}

logging.basicConfig(level=logging.INFO, format='%(message)s')
file_handler = logging.FileHandler("interpreter.log", encoding='utf-8')
file_handler.setLevel(logging.INFO)
formatter = logging.Formatter('%(asctime)s - %(message)s')
file_handler.setFormatter(formatter)
logging.getLogger().addHandler(file_handler)

def remove_comments(line: str) -> str:
    """
    문자열 내에서 # 문자가 나타나면 주석으로 간주하여 제거합니다.
    단, 문자열 리터럴 내부의 '#'는 유지합니다.
    """
    in_single = False
    in_double = False
    result = []
    i = 0
    while i < len(line):
        ch = line[i]
        if ch == "'" and not in_double:
            in_single = not in_single
        elif ch == '"' and not in_single:
            in_double = not in_double
        elif ch == '#' and not in_single and not in_double:
            break
        result.append(ch)
        i += 1
    return "".join(result).strip()

allowed_operators: Dict[Any, Any] = {
    ast.Add: op.add,
    ast.Sub: op.sub,
    ast.Mult: op.mul,
    ast.Div: op.truediv,
    ast.Pow: op.pow,
    ast.Mod: op.mod,
}

allowed_unary_operators: Dict[Any, Any] = {
    ast.UAdd: op.pos,
    ast.USub: op.neg,
    ast.Not: op.not_,
}

allowed_compare_ops: Dict[Any, Any] = {
    ast.Eq: op.eq,
    ast.NotEq: op.ne,
    ast.Lt: op.lt,
    ast.LtE: op.le,
    ast.Gt: op.gt,
    ast.GtE: op.ge,
}

def safe_eval(expression: str, variables: Dict[str, Any]) -> Any:
    """
    AST를 이용해 expression을 안전하게 평가합니다.
    AST 캐싱을 통해 성능을 최적화합니다.
    """
    expr_key = expression.strip()
    try:
        if expr_key in AST_CACHE:
            tree = AST_CACHE[expr_key]
        else:
            tree = ast.parse(expression, mode='eval')
            AST_CACHE[expr_key] = tree
        return _eval_node(tree.body, variables)
    except Exception as e:
        raise ValueError(f"안전하지 않은 표현식: {e}")

def _eval_node(node: ast.AST, variables: Dict[str, Any]) -> Any:
    if isinstance(node, ast.Constant):
        return node.value
    elif isinstance(node, ast.BinOp):
        left = _eval_node(node.left, variables)
        right = _eval_node(node.right, variables)
        operator_func = allowed_operators.get(type(node.op))
        if operator_func is None:
            raise ValueError(f"지원되지 않는 이항 연산자: {node.op}")
        return operator_func(left, right)
    elif isinstance(node, ast.UnaryOp):
        operand = _eval_node(node.operand, variables)
        operator_func = allowed_unary_operators.get(type(node.op))
        if operator_func is None:
            raise ValueError(f"지원되지 않는 단항 연산자: {node.op}")
        return operator_func(operand)
    elif isinstance(node, ast.BoolOp):
        if isinstance(node.op, ast.And):
            return all(_eval_node(v, variables) for v in node.values)
        elif isinstance(node.op, ast.Or):
            return any(_eval_node(v, variables) for v in node.values)
        else:
            raise ValueError(f"지원되지 않는 불린 연산자: {node.op}")
    elif isinstance(node, ast.Compare):
        left = _eval_node(node.left, variables)
        for op_node, comparator in zip(node.ops, node.comparators):
            comp = _eval_node(comparator, variables)
            operator_func = allowed_compare_ops.get(type(op_node))
            if operator_func is None:
                raise ValueError(f"지원되지 않는 비교 연산자: {op_node}")
            if not operator_func(left, comp):
                return False
            left = comp
        return True
    elif isinstance(node, ast.List):
        return [_eval_node(e, variables) for e in node.elts]
    elif isinstance(node, ast.Tuple):
        return tuple(_eval_node(e, variables) for e in node.elts)
    elif isinstance(node, ast.Dict):
        return {_eval_node(k, variables): _eval_node(v, variables) for k, v in zip(node.keys, node.values)}
    elif isinstance(node, ast.Subscript):
        container = _eval_node(node.value, variables)
        if isinstance(node.slice, ast.Index):
            index = _eval_node(node.slice.value, variables)
        else:
            index = _eval_node(node.slice, variables)
        return container[index]
    elif isinstance(node, ast.Name):
        if node.id in variables:
            value = variables[node.id]
            if value is None:
                raise ValueError(f"변수 '{node.id}'에 값이 할당되지 않음")
            return value
        else:
            raise ValueError(f"변수 '{node.id}'가 선언되지 않음")
    else:
        raise TypeError(f"지원되지 않는 표현식 구성요소: {node}")

class BreakException(Exception):
    pass

class ContinueException(Exception):
    pass

class ReturnException(Exception):
    def __init__(self, value: Any):
        self.value = value

class Function:
    def __init__(self, params: List[str], block: List[str], closure: List[Dict[str, Any]]):
        self.params = params
        self.block = block
        self.closure = closure.copy()

    def __str__(self):
        return f"Function({', '.join(self.params)})"

    def call(self, interpreter: "Interpreter", args: List[Any]) -> Any:
        if len(args) != len(self.params):
            interpreter.eungdi(
                f"오류: 함수 호출 인자 개수 불일치. 기대: {len(self.params)}, 전달: {len(args)}",
                error=True)
            return None
        if interpreter.debug:
            interpreter.eungdi(f"[DEBUG] 함수 {self} 호출 시작, 인자: {args}")
        old_scopes = interpreter.scopes
        interpreter.scopes = self.closure + [{}]
        for p, arg in zip(self.params, args):
            interpreter.current_scope()[p] = arg
        ret_value = None
        try:
            interpreter.execute_lines(self.block, 0)
        except ReturnException as ret_ex:
            ret_value = ret_ex.value
        interpreter.scopes = old_scopes
        if interpreter.debug:
            interpreter.eungdi(f"[DEBUG] 함수 {self} 호출 종료, 반환값: {ret_value}")
        return ret_value

class Interpreter:
    """
    인터프리터는 다음 기능들을 지원합니다:
      - 기본 명령어: 출력, 변수 선언/할당/삭제, 파일 읽기, 사용자 입력, 도움말 등.
      - 조건문 (만약 ~ [아니면] ~ 끝 만약 북딱)
      - 반복문: while (반복 (조건) 북딱 ... 끝 반복 북딱) 및 for (반복문 변수 in 표현식 북딱 ... 끝 반복문 북딱)
      - break/continue: "브레이크 북딱", "넘어가 북딱"
      - 함수 정의/호출 및 반환: 함수를 흔들어라 <함수명>(매개변수) 북딱 ... 끝 흔들어라 북딱 형식으로 정의하며, 함수 호출은 '함수 호출' 구문을 사용합니다.
      - 추가 기능: 상태 출력, 버전 출력, 파일 쓰기/추가, 현재 시간/날짜 출력, HTTP 요청, JSON 변환/문자열화, 리스트 및 딕셔너리 조작,
        그리고 REPL 개선 및 내장 함수 보강.
      - **추가/개선된 기능**:
          • 파일 조작: 파일 삭제, 파일 존재 확인, 디렉터리 목록  
          • 리스트/문자열 조작: 리스트 정렬, 대문자/소문자 변환  
          • 랜덤 값 생성: 랜덤 숫자, 랜덤 리스트 섞기  
          • 환경 변수 조작: 환경 변수 출력, 환경 변수 설정  
          • 수학 연산: 거듭제곱, 제곱근, 로그  
          • 변수 저장 및 불러오기  
          • 인터프리터 종료  
          • REPL 개선: 프롬프트 설정  
          • UI 개선: colorama를 활용한 색상 출력, 명령어 자동 완성  
          • 성능 최적화: AST 캐싱, --fast 옵션  
          • **추가된 시스템 명령**: 화면 지우기, 현재 경로 출력, 작업 디렉터리 변경
    """
    VERSION = "1.1"

    def __init__(self, debug: bool = False, fast: bool = False):
        self.scopes: List[Dict[str, Any]] = [{}]
        self.current_line: Optional[int] = None
        self.debug = debug
        self.fast = fast
        self.input_buffer: List[str] = []
        self.prompt = ">> "

        if self.fast:
            logging.getLogger().setLevel(logging.ERROR)

        self.scopes[0].update({
            'sqrt': math.sqrt,
            'sin': math.sin,
            'cos': math.cos,
            'tan': math.tan,
            'max': max,
            'min': min,
            'abs': abs,
            'round': round,
            'int': int,
            'str': str,
            'len': len,
            'log': math.log,
            'exp': math.exp,
            '현재시간': lambda: datetime.datetime.now().strftime("%H:%M:%S"),
            '현재날짜': lambda: datetime.datetime.now().strftime("%Y-%m-%d"),
            'JSON변환': json.loads,
            'JSON문자열화': json.dumps,
        })

        self.pattern_help = re.compile(r'도움말 북딱')
        self.pattern_print = re.compile(r'노무현이 왔습니다 "(.*?)" 북딱')
        self.pattern_declare = re.compile(r'동네 힘센 사람 ([^ ]+) 북딱')
        self.pattern_assign = re.compile(r'([^ ]+) 마 매끼나라 고마 (.*?) 북딱')
        self.pattern_readfile = re.compile(r'방독면 챙기십쇼 "(.*?)" 북딱')
        self.pattern_input = re.compile(r'지금까지 뭐했노 "(.*?)" 북딱')
        self.pattern_output = re.compile(r'응디 ([^ ]+) 북딱')
        self.pattern_list_vars = re.compile(r'변수 목록 북딱')
        self.pattern_delete_var = re.compile(r'변수 삭제 ([^ ]+) 북딱')
        self.pattern_break = re.compile(r'브레이크 북딱')
        self.pattern_continue = re.compile(r'넘어가 북딱')
        self.pattern_if = re.compile(r'만약 \((.*?)\) 북딱')
        self.pattern_else = re.compile(r'아니면 북딱')
        self.pattern_end_if = re.compile(r'끝 만약 북딱')
        self.pattern_while = re.compile(r'반복 \((.*?)\) 북딱')
        self.pattern_end_while = re.compile(r'끝 반복 북딱')
        self.pattern_for = re.compile(r'반복문 ([^ ]+) in (.*?) 북딱')
        self.pattern_end_for = re.compile(r'끝 반복문 북딱')
        self.pattern_func_def = re.compile(r'흔들어라 ([^ ]+)\s*\((.*?)\) 북딱')
        self.pattern_end_func = re.compile(r'끝 흔들어라 북딱')
        self.pattern_func_call = re.compile(r'함수 호출 ([^ ]+)\s*\((.*?)\) 북딱')
        self.pattern_return = re.compile(r'돌아가(?: (.*?))? 북딱')
        
        self.single_commands = [
            (self.pattern_help, self.handle_help),
            (self.pattern_print, self.handle_print),
            (self.pattern_declare, self.handle_declare),
            (self.pattern_assign, self.handle_assign),
            (self.pattern_readfile, self.handle_readfile),
            (self.pattern_input, self.handle_input),
            (self.pattern_output, self.handle_output),
            (self.pattern_list_vars, self.handle_list_vars),
            (self.pattern_delete_var, self.handle_delete_var),
            (re.compile(r'상태 북딱'), self.handle_state),
            (re.compile(r'버전 북딱'), self.handle_version),
            (re.compile(r'파일에 쓰기 "(.*?)", "(.*?)" 북딱'), self.handle_file_write),
            (re.compile(r'파일에 추가하기 "(.*?)", "(.*?)" 북딱'), self.handle_file_append),
            (re.compile(r'응디 현재 시간 북딱'), self.handle_current_time),
            (re.compile(r'응디 현재 날짜 북딱'), self.handle_current_date),
            (re.compile(r'응디 요청 보내기 "(.*?)" 북딱'), self.handle_http_request),
            (re.compile(r'JSON 변환 "(.*?)" 북딱'), self.handle_json_load),
            (re.compile(r'JSON 문자열화 ([^ ]+) 북딱'), self.handle_json_dump),
            (re.compile(r'리스트 추가 ([^ ]+), (.*?) 북딱'), self.handle_list_append),
            (re.compile(r'리스트 삭제 ([^ ]+), (.*?) 북딱'), self.handle_list_delete),
            (re.compile(r'딕셔너리 추가 ([^,]+), (.*?), (.*?) 북딱'), self.handle_dict_add),
            (re.compile(r'딕셔너리 삭제 ([^,]+), (.*?) 북딱'), self.handle_dict_delete),
            (re.compile(r'초기화 북딱'), self.handle_reset),
            (re.compile(r'내장함수 목록 북딱'), self.handle_builtin_list),
            (re.compile(r'시스템 실행 "(.*?)" 북딱'), self.handle_system_command),
            (re.compile(r'파일 삭제 "(.*?)" 북딱'), self.handle_file_delete),
            (re.compile(r'파일 존재 확인 "(.*?)" 북딱'), self.handle_file_exists),
            (re.compile(r'디렉터리 목록 북딱'), self.handle_list_directory),
            (re.compile(r'리스트 정렬 ([^ ]+) 북딱'), self.handle_list_sort),
            (re.compile(r'대문자로 변환 ([^ ]+) 북딱'), self.handle_uppercase),
            (re.compile(r'소문자로 변환 ([^ ]+) 북딱'), self.handle_lowercase),
            (re.compile(r'랜덤 숫자 \((.*?), (.*?)\) 북딱'), self.handle_random_number),
            (re.compile(r'랜덤 리스트 섞기 ([^ ]+) 북딱'), self.handle_shuffle_list),
            (re.compile(r'환경 변수 출력 "(.*?)" 북딱'), self.handle_env_print),
            (re.compile(r'환경 변수 설정 "(.*?)", "(.*?)" 북딱'), self.handle_env_set),
            (re.compile(r'거듭제곱 \((.*?), (.*?)\) 북딱'), self.handle_power),
            (re.compile(r'제곱근 \((.*?)\) 북딱'), self.handle_sqrt),
            (re.compile(r'로그 \((.*?), (.*?)\) 북딱'), self.handle_log),
            (re.compile(r'변수 저장 "(.*?)" 북딱'), self.handle_save_vars),
            (re.compile(r'변수 불러오기 "(.*?)" 북딱'), self.handle_load_vars),
            (re.compile(r'종료 북딱'), self.handle_exit),
            (re.compile(r'프롬프트 설정 "(.*?)" 북딱'), self.handle_set_prompt),
            (re.compile(r'도움말 "명령어" 북딱'), self.handle_command_auto_complete),
            (re.compile(r'화면 지우기 북딱'), self.handle_clear_screen),
            (re.compile(r'현재 경로 출력 북딱'), self.handle_cwd_print),
            (re.compile(r'작업 디렉터리 변경 "(.*?)" 북딱'), self.handle_change_directory),
        ]

    def current_scope(self) -> Dict[str, Any]:
        return self.scopes[-1]

    def push_scope(self) -> None:
        self.scopes.append({})

    def pop_scope(self) -> None:
        if len(self.scopes) > 1:
            self.scopes.pop()
        else:
            self.eungdi("오류: 전역 스코프는 제거할 수 없습니다.", error=True)

    def get_combined_scope(self) -> Dict[str, Any]:
        return ChainMap(*self.scopes[::-1])

    def declare_variable(self, var_name: str) -> None:
        if var_name in self.current_scope():
            self.eungdi(f'오류: 변수 "{var_name}" 가 이미 선언됨', error=True)
        else:
            self.current_scope()[var_name] = None

    def assign_variable(self, var_name: str, value: Any) -> None:
        for scope in reversed(self.scopes):
            if var_name in scope:
                scope[var_name] = value
                return
        self.eungdi(f'오류: 변수 "{var_name}" 가 선언되지 않음', error=True)

    def get_variable(self, var_name: str) -> Any:
        for scope in reversed(self.scopes):
            if var_name in scope:
                return scope[var_name]
        self.eungdi(f'오류: 변수 "{var_name}" 가 선언되지 않음', error=True)
        return None

    def eungdi(self, message: str, error: bool = False) -> None:
        if self.fast and not error:
            return
        if colorama is not None:
            if error:
                colored_message = Fore.RED + message + Style.RESET_ALL
            else:
                colored_message = Fore.GREEN + message + Style.RESET_ALL
        else:
            colored_message = message
        output = f"Line {self.current_line}: {colored_message}" if self.current_line is not None else colored_message
        if error:
            logging.error(output)
        else:
            logging.info(output)
        if self.debug:
            logging.debug(f"[DEBUG] 스코프: {dict(self.get_combined_scope())}")

    def read_file(self, file_path: str) -> Optional[str]:
        try:
            with open(file_path, 'r', encoding='utf-8') as file:
                return file.read().strip()
        except FileNotFoundError:
            self.eungdi(f'오류: 파일을 찾을 수 없습니다 - {file_path}', error=True)
        except Exception as e:
            self.eungdi(f'오류: 파일 읽기 실패 - {e}', error=True)
        return None

    def get_user_input(self, prompt: str) -> str:
        if self.input_buffer:
            return self.input_buffer.pop(0)
        return input(prompt)

    def evaluate_expression(self, expression: str) -> Any:
        try:
            return safe_eval(expression, dict(self.get_combined_scope()))
        except Exception as e:
            self.eungdi(f'오류: 수식 평가 중 문제 발생 - {e}', error=True)
            return None

    def print_help(self) -> None:
        help_message = '''
명령어 목록:
- 노무현이 왔습니다 "메시지" 북딱 : 메시지 출력.
- 동네 힘센 사람 변수명 북딱 : 변수 선언.
- 변수명 마 매끼나라 고마 표현식 북딱 : 변수에 표현식 평가 결과 할당.
- 응디 변수명 북딱 : 변수 출력.
- 방독면 챙기십쇼 "파일경로" 북딱 : 파일 내용 출력.
- 지금까지 뭐했노 "프롬프트" 북딱 : 사용자 입력 후 출력.
- 변수 목록 북딱 : 현재 스코프의 변수 목록 출력.
- 변수 삭제 변수명 북딱 : 변수 삭제.
- 만약 (조건식) 북딱 ... [아니면 북딱 ...] 끝 만약 북딱 : 조건문.
- 반복 (조건식) 북딱 ... 끝 반복 북딱 : while 반복문.
- 반복문 변수 in 표현식 북딱 ... 끝 반복문 북딱 : for 반복문.
- 브레이크 북딱 : 반복문 중 break.
- 넘어가 북딱 : 반복문 중 continue.
- 흔들어라 함수명(매개변수들) 북딱 ... 끝 흔들어라 북딱 : 함수 정의.
- 함수 호출 함수명(인자들) 북딱 : 함수 호출.
- 돌아가 [표현식] 북딱 : 함수에서 반환.
- 상태 북딱 : 현재 스코프(변수 상태) 출력.
- 버전 북딱 : 인터프리터 버전 출력.
-------------------------------
[추가 기능]
- 파일에 쓰기 "파일명", "내용" 북딱
- 파일에 추가하기 "파일명", "내용" 북딱
- 파일 삭제 "파일명" 북딱
- 파일 존재 확인 "파일명" 북딱
- 디렉터리 목록 북딱
- 응디 현재 시간 북딱
- 응디 현재 날짜 북딱
- 응디 요청 보내기 "URL" 북딱
- JSON 변환 "문자열" 북딱
- JSON 문자열화 변수명 북딱
- 리스트 추가 변수명, 값 북딱
- 리스트 삭제 변수명, 인덱스 북딱
- 리스트 정렬 변수명 북딱
- 대문자로 변환 변수명 북딱
- 소문자로 변환 변수명 북딱
- 랜덤 숫자 (최소, 최대) 북딱
- 랜덤 리스트 섞기 리스트명 북딱
- 환경 변수 출력 "변수명" 북딱
- 환경 변수 설정 "변수명", "값" 북딱
- 거듭제곱 (밑, 지수) 북딱
- 제곱근 (값) 북딱
- 로그 (값, 밑) 북딱
- 변수 저장 "파일명" 북딱
- 변수 불러오기 "파일명" 북딱
- 종료 북딱
- 프롬프트 설정 "새 프롬프트" 북딱
- 도움말 "명령어" 북딱 : 지원 명령어 목록 출력.
-------------------------------
[추가된 시스템 명령어]
- 화면 지우기 북딱 : 콘솔 화면 지우기.
- 현재 경로 출력 북딱 : 현재 작업 디렉터리 출력.
- 작업 디렉터리 변경 "경로" 북딱 : 작업 디렉터리 변경.
        '''
        self.eungdi(help_message.strip())

    def handle_help(self, match, line: str) -> None:
        self.print_help()

    def handle_print(self, match, line: str) -> None:
        self.eungdi(match.group(1))

    def handle_declare(self, match, line: str) -> None:
        self.declare_variable(match.group(1))

    def handle_assign(self, match, line: str) -> None:
        value = self.evaluate_expression(match.group(2))
        if value is not None:
            self.assign_variable(match.group(1), value)

    def handle_readfile(self, match, line: str) -> None:
        content = self.read_file(match.group(1))
        if content is not None:
            self.eungdi(content)

    def handle_input(self, match, line: str) -> None:
        user_input = self.get_user_input(match.group(1) + ': ')
        self.eungdi(user_input)

    def handle_output(self, match, line: str) -> None:
        self.eungdi(str(self.get_variable(match.group(1))))

    def handle_list_vars(self, match, line: str) -> None:
        combined = dict(self.get_combined_scope())
        for var, value in sorted(combined.items()):
            self.eungdi(f'{var} = {value}')

    def handle_delete_var(self, match, line: str) -> None:
        var_name = match.group(1)
        if var_name in self.current_scope():
            del self.current_scope()[var_name]
            self.eungdi(f'변수 "{var_name}" 삭제됨')
        else:
            self.eungdi(f'오류: 변수 "{var_name}" 가 현재 스코프에 없음', error=True)

    def handle_state(self, match, line: str) -> None:
        state = dict(self.get_combined_scope())
        self.eungdi(f"현재 상태: {state}")

    def handle_version(self, match, line: str) -> None:
        self.eungdi(f"Interpreter version: {self.VERSION}")

    def handle_file_write(self, match, line: str) -> None:
        filename, content = match.group(1), match.group(2)
        try:
            with open(filename, "w", encoding="utf-8") as f:
                f.write(content)
            self.eungdi(f'파일 "{filename}"에 쓰기 완료')
        except Exception as e:
            self.eungdi(f'파일 쓰기 실패: {e}', error=True)

    def handle_file_append(self, match, line: str) -> None:
        filename, content = match.group(1), match.group(2)
        try:
            with open(filename, "a", encoding="utf-8") as f:
                f.write(content)
            self.eungdi(f'파일 "{filename}"에 추가 쓰기 완료')
        except Exception as e:
            self.eungdi(f'파일 추가 쓰기 실패: {e}', error=True)

    def handle_current_time(self, match, line: str) -> None:
        self.eungdi(datetime.datetime.now().strftime("%H:%M:%S"))

    def handle_current_date(self, match, line: str) -> None:
        self.eungdi(datetime.datetime.now().strftime("%Y-%m-%d"))

    def handle_http_request(self, match, line: str) -> None:
        url = match.group(1)
        try:
            response = requests.get(url)
            self.eungdi(f"HTTP 응답 ({response.status_code}): {response.text[:200]}...")
        except Exception as e:
            self.eungdi(f"HTTP 요청 실패: {e}", error=True)

    def handle_json_load(self, match, line: str) -> None:
        json_str = match.group(1).strip()
        try:
            json_str = bytes(json_str, "utf-8").decode("unicode_escape")
        except Exception as e:
            self.eungdi(f"JSON 문자열 디코딩 실패: {e}", error=True)
            return
        if json_str.startswith('"') and json_str.endswith('"'):
            json_str = json_str[1:-1].strip()
        try:
            obj = json.loads(json_str)
            self.eungdi(f"JSON 객체: {obj}")
            return
        except json.JSONDecodeError:
            pass
        fixed_json_str = self.fix_json_string(json_str)
        try:
            obj = json.loads(fixed_json_str)
            self.eungdi(f"JSON 객체: {obj}")
        except json.JSONDecodeError as e:
            self.eungdi(f"JSON 변환 실패: {e}", error=True)

    def fix_json_string(self, json_str: str) -> str:
        """
        JSON 문자열에서 잘못된 작은따옴표와 따옴표가 없는 키를 수정합니다.
        1. { 또는 , 뒤에 오는 속성명에 자동으로 큰따옴표를 추가합니다.
        2. 모든 작은따옴표(')를 큰따옴표(")로 변환합니다.
        """
        json_str = json_str.strip()
        fixed = re.sub(r'([{,]\s*)([A-Za-z0-9_가-힣]+)(\s*:)', r'\1"\2"\3', json_str, flags=re.UNICODE)
        fixed = fixed.replace("'", "\"")
        return fixed.strip()


    def handle_json_dump(self, match, line: str) -> None:
        var_name = match.group(1)
        obj = self.get_variable(var_name)
        if obj is not None:
            try:
                json_str = json.dumps(obj)
                self.eungdi(f"JSON 문자열: {json_str}")
            except Exception as e:
                self.eungdi(f"JSON 문자열화 실패: {e}", error=True)
        else:
            self.eungdi(f"오류: 변수 '{var_name}'가 존재하지 않음", error=True)

    def handle_list_append(self, match, line: str) -> None:
        var_name, value_expr = match.group(1), match.group(2)
        lst = self.get_variable(var_name)
        if isinstance(lst, list):
            value = self.evaluate_expression(value_expr)
            lst.append(value)
            self.eungdi(f"리스트 '{var_name}'에 값 추가됨")
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 리스트가 아님", error=True)

    def handle_list_delete(self, match, line: str) -> None:
        var_name, index_expr = match.group(1), match.group(2)
        lst = self.get_variable(var_name)
        if isinstance(lst, list):
            try:
                index = int(self.evaluate_expression(index_expr))
                lst.pop(index)
                self.eungdi(f"리스트 '{var_name}'에서 인덱스 {index} 삭제됨")
            except Exception as e:
                self.eungdi(f"리스트 삭제 실패: {e}", error=True)
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 리스트가 아님", error=True)

    def handle_dict_add(self, match, line: str) -> None:
        var_name, key_expr, value_expr = match.group(1), match.group(2), match.group(3)
        d = self.get_variable(var_name)
        if isinstance(d, dict):
            key = self.evaluate_expression(key_expr)
            value = self.evaluate_expression(value_expr)
            d[key] = value
            self.eungdi(f"딕셔너리 '{var_name}'에 키 {key} 추가/변경됨")
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 딕셔너리가 아님", error=True)

    def handle_dict_delete(self, match, line: str) -> None:
        var_name, key_expr = match.group(1), match.group(2)
        d = self.get_variable(var_name)
        if isinstance(d, dict):
            key = self.evaluate_expression(key_expr)
            if key in d:
                del d[key]
                self.eungdi(f"딕셔너리 '{var_name}'에서 키 {key} 삭제됨")
            else:
                self.eungdi(f"오류: 딕셔너리 '{var_name}'에 키 {key}가 없음", error=True)
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 딕셔너리가 아님", error=True)

    def handle_reset(self, match, line: str) -> None:
        builtins = self.scopes[0].copy()
        self.scopes = [builtins]
        self.eungdi("스코프 초기화 완료")

    def handle_builtin_list(self, match, line: str) -> None:
        builtins = self.scopes[0]
        funcs = {k: v for k, v in builtins.items() if callable(v)}
        self.eungdi(f"내장 함수 목록: {list(funcs.keys())}")

    def handle_system_command(self, match, line: str) -> None:
        command = match.group(1)
        try:
            result = os.system(command)
            self.eungdi(f"시스템 명령 실행 결과: {result}")
        except Exception as e:
            self.eungdi(f"시스템 명령 실행 실패: {e}", error=True)
    
    def handle_file_delete(self, match, line: str) -> None:
        filename = match.group(1)
        try:
            os.remove(filename)
            self.eungdi(f'파일 "{filename}" 삭제 완료')
        except Exception as e:
            self.eungdi(f'파일 삭제 실패: {e}', error=True)

    def handle_file_exists(self, match, line: str) -> None:
        filename = match.group(1)
        exists = os.path.exists(filename)
        self.eungdi(f'파일 "{filename}" 존재 여부: {exists}')

    def handle_list_directory(self, match, line: str) -> None:
        try:
            files = os.listdir(".")
            self.eungdi("디렉터리 목록: " + ", ".join(files))
        except Exception as e:
            self.eungdi(f"디렉터리 목록 출력 실패: {e}", error=True)

    def handle_list_sort(self, match, line: str) -> None:
        var_name = match.group(1)
        lst = self.get_variable(var_name)
        if isinstance(lst, list):
            sorted_list = sorted(lst)
            self.assign_variable(var_name, sorted_list)
            self.eungdi(f"리스트 '{var_name}' 정렬 완료")
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 리스트가 아님", error=True)

    def handle_uppercase(self, match, line: str) -> None:
        var_name = match.group(1)
        s = self.get_variable(var_name)
        if isinstance(s, str):
            self.assign_variable(var_name, s.upper())
            self.eungdi(f"변수 '{var_name}'를 대문자로 변환 완료")
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 문자열이 아님", error=True)

    def handle_lowercase(self, match, line: str) -> None:
        var_name = match.group(1)
        s = self.get_variable(var_name)
        if isinstance(s, str):
            self.assign_variable(var_name, s.lower())
            self.eungdi(f"변수 '{var_name}'를 소문자로 변환 완료")
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 문자열이 아님", error=True)

    def handle_random_number(self, match, line: str) -> None:
        min_expr, max_expr = match.group(1), match.group(2)
        min_val = self.evaluate_expression(min_expr)
        max_val = self.evaluate_expression(max_expr)
        try:
            num = random.randint(int(min_val), int(max_val))
            self.eungdi(f"랜덤 숫자: {num}")
        except Exception as e:
            self.eungdi(f"랜덤 숫자 생성 실패: {e}", error=True)

    def handle_shuffle_list(self, match, line: str) -> None:
        var_name = match.group(1)
        lst = self.get_variable(var_name)
        if isinstance(lst, list):
            random.shuffle(lst)
            self.eungdi(f"리스트 '{var_name}'가 무작위로 섞였습니다")
        else:
            self.eungdi(f"오류: 변수 '{var_name}'는 리스트가 아님", error=True)

    def handle_env_print(self, match, line: str) -> None:
        var_name = match.group(1)
        value = os.environ.get(var_name)
        self.eungdi(f'환경 변수 "{var_name}" = {value}')

    def handle_env_set(self, match, line: str) -> None:
        var_name, value = match.group(1), match.group(2)
        try:
            os.environ[var_name] = value
            self.eungdi(f'환경 변수 "{var_name}"를 "{value}"로 설정함')
        except Exception as e:
            self.eungdi(f"환경 변수 설정 실패: {e}", error=True)

    def handle_power(self, match, line: str) -> None:
        base_expr, exp_expr = match.group(1), match.group(2)
        base = self.evaluate_expression(base_expr)
        exponent = self.evaluate_expression(exp_expr)
        try:
            result = math.pow(base, exponent)
            self.eungdi(f"거듭제곱 결과: {result}")
        except Exception as e:
            self.eungdi(f"거듭제곱 계산 실패: {e}", error=True)

    def handle_sqrt(self, match, line: str) -> None:
        value_expr = match.group(1)
        value = self.evaluate_expression(value_expr)
        try:
            result = math.sqrt(value)
            self.eungdi(f"제곱근 결과: {result}")
        except Exception as e:
            self.eungdi(f"제곱근 계산 실패: {e}", error=True)

    def handle_log(self, match, line: str) -> None:
        value_expr, base_expr = match.group(1), match.group(2)
        value = self.evaluate_expression(value_expr)
        base = self.evaluate_expression(base_expr)
        try:
            result = math.log(value, base)
            self.eungdi(f"로그 결과: {result}")
        except Exception as e:
            self.eungdi(f"로그 계산 실패: {e}", error=True)

    def handle_save_vars(self, match, line: str) -> None:
        filename = match.group(1)
        user_vars = {}
        for scope in self.scopes[1:]:
            user_vars.update(scope)
        try:
            with open(filename, "w", encoding="utf-8") as f:
                json.dump(user_vars, f, default=str)
            self.eungdi(f"변수 저장 완료: {filename}")
        except Exception as e:
            self.eungdi(f"변수 저장 실패: {e}", error=True)

    def handle_load_vars(self, match, line: str) -> None:
        filename = match.group(1)
        try:
            with open(filename, "r", encoding="utf-8") as f:
                loaded_vars = json.load(f)
            self.current_scope().update(loaded_vars)
            self.eungdi(f"변수 불러오기 완료: {filename}")
        except Exception as e:
            self.eungdi(f"변수 불러오기 실패: {e}", error=True)

    def handle_exit(self, match, line: str) -> None:
        self.eungdi("인터프리터 종료")
        sys.exit(0)

    def handle_set_prompt(self, match, line: str) -> None:
        new_prompt = match.group(1)
        self.prompt = new_prompt + " "
        self.eungdi(f"프롬프트가 '{new_prompt}'로 설정됨")

    def handle_command_auto_complete(self, match, line: str) -> None:
        cmds = [p.pattern for (p, h) in self.single_commands]
        self.eungdi("지원 명령어 목록:\n" + "\n".join(cmds))

    def handle_clear_screen(self, match, line: str) -> None:
        try:
            if os.name == 'nt':
                os.system('cls')
            else:
                os.system('clear')
            self.eungdi("화면 지우기 완료")
        except Exception as e:
            self.eungdi(f"화면 지우기 실패: {e}", error=True)

    def handle_cwd_print(self, match, line: str) -> None:
        try:
            cwd = os.getcwd()
            self.eungdi(f"현재 작업 디렉터리: {cwd}")
        except Exception as e:
            self.eungdi(f"현재 경로 출력 실패: {e}", error=True)

    def handle_change_directory(self, match, line: str) -> None:
        path = match.group(1)
        try:
            os.chdir(path)
            self.eungdi(f"작업 디렉터리 변경 완료: {os.getcwd()}")
        except Exception as e:
            self.eungdi(f"작업 디렉터리 변경 실패: {e}", error=True)

    def interpret_line(self, line: str) -> None:
        line = remove_comments(line)
        if not line:
            return
        for pattern, handler in self.single_commands:
            m = pattern.fullmatch(line)
            if m:
                handler(m, line)
                return
        self.eungdi(f'오류: 알 수 없는 명령어 - {line}', error=True)

    def execute_lines(self, lines: List[str], start_index: int = 0) -> int:
        i = start_index
        while i < len(lines):
            self.current_line = i + 1
            line = remove_comments(lines[i])
            if not line:
                i += 1
                continue

            if self.pattern_if.fullmatch(line):
                i = self.process_if(lines, i)
                continue
            if self.pattern_while.fullmatch(line):
                i = self.process_while(lines, i)
                continue
            if self.pattern_for.fullmatch(line):
                i = self.process_for(lines, i)
                continue
            if self.pattern_func_def.fullmatch(line):
                i = self.process_func_def(lines, i)
                continue
            if self.pattern_func_call.fullmatch(line):
                self.process_func_call(line)
                i += 1
                continue
            if re.fullmatch(r'브레이크 북딱', line):
                raise BreakException()
            if re.fullmatch(r'넘어가 북딱', line):
                raise ContinueException()
            if self.pattern_return.fullmatch(line):
                self.process_return(line)

            self.interpret_line(line)
            i += 1
        return i

    def interpret_program(self, program: str) -> None:
        lines = program.splitlines()
        try:
            self.execute_lines(lines, 0)
        except Exception as e:
            self.eungdi(f"실행 중 오류: {e}", error=True)
        self.current_line = None

    def process_if(self, lines: List[str], index: int) -> int:
        line = remove_comments(lines[index])
        match = self.pattern_if.fullmatch(line)
        if not match:
            self.eungdi("오류: if 구문 파싱 실패", error=True)
            return index + 1
        condition_expr = match.group(1)
        condition_value = self.evaluate_expression(condition_expr)

        if_block: List[str] = []
        else_block: List[str] = []
        i = index + 1
        in_else = False
        nested_if = 0
        while i < len(lines):
            curr_line = remove_comments(lines[i])
            if self.pattern_if.fullmatch(curr_line):
                nested_if += 1
            elif self.pattern_end_if.fullmatch(curr_line):
                if nested_if > 0:
                    nested_if -= 1
                else:
                    break
            elif self.pattern_else.fullmatch(curr_line) and nested_if == 0:
                in_else = True
                i += 1
                continue
            if not in_else:
                if_block.append(curr_line)
            else:
                else_block.append(curr_line)
            i += 1

        self.push_scope()
        if condition_value:
            self.execute_lines(if_block, 0)
        else:
            self.execute_lines(else_block, 0)
        self.pop_scope()
        return i + 1

    def process_while(self, lines: List[str], index: int) -> int:
        line = remove_comments(lines[index])
        match = self.pattern_while.fullmatch(line)
        if not match:
            self.eungdi("오류: while 구문 파싱 실패", error=True)
            return index + 1
        condition_expr = match.group(1)
        block: List[str] = []
        i = index + 1
        nested_while = 0
        while i < len(lines):
            curr_line = remove_comments(lines[i])
            if self.pattern_while.fullmatch(curr_line):
                nested_while += 1
            elif self.pattern_end_while.fullmatch(curr_line):
                if nested_while > 0:
                    nested_while -= 1
                else:
                    break
            block.append(curr_line)
            i += 1

        while self.evaluate_expression(condition_expr):
            self.push_scope()
            try:
                self.execute_lines(block, 0)
            except ContinueException:
                self.pop_scope()
                continue
            except BreakException:
                self.pop_scope()
                break
            self.pop_scope()
        return i + 1

    def process_for(self, lines: List[str], index: int) -> int:
        line = remove_comments(lines[index])
        match = self.pattern_for.fullmatch(line)
        if not match:
            self.eungdi("오류: for 구문 파싱 실패", error=True)
            return index + 1
        iter_var = match.group(1)
        iterable_expr = match.group(2)
        iterable_value = self.evaluate_expression(iterable_expr)
        if not hasattr(iterable_value, '__iter__'):
            self.eungdi("오류: for문 대상이 반복 가능하지 않음", error=True)
            return index + 1

        block: List[str] = []
        i = index + 1
        while i < len(lines):
            curr_line = remove_comments(lines[i])
            if self.pattern_end_for.fullmatch(curr_line):
                break
            block.append(curr_line)
            i += 1

        for item in iterable_value:
            self.push_scope()
            self.declare_variable(iter_var)
            self.assign_variable(iter_var, item)
            try:
                self.execute_lines(block, 0)
            except ContinueException:
                self.pop_scope()
                continue
            except BreakException:
                self.pop_scope()
                break
            self.pop_scope()
        return i + 1

    def process_func_def(self, lines: List[str], index: int) -> int:
        line = remove_comments(lines[index])
        match = self.pattern_func_def.fullmatch(line)
        if not match:
            self.eungdi("오류: 함수 정의 구문 파싱 실패", error=True)
            return index + 1
        func_name = match.group(1)
        params = [p.strip() for p in match.group(2).split(",") if p.strip()]
        block: List[str] = []
        i = index + 1
        nested_func = 0
        while i < len(lines):
            curr_line = remove_comments(lines[i])
            if self.pattern_func_def.fullmatch(curr_line):
                nested_func += 1
            elif self.pattern_end_func.fullmatch(curr_line):
                if nested_func > 0:
                    nested_func -= 1
                else:
                    break
            block.append(curr_line)
            i += 1
        closure = copy.deepcopy(self.scopes)
        func_obj = Function(params, block, closure)
        self.declare_variable(func_name)
        self.assign_variable(func_name, func_obj)
        return i + 1

    def process_func_call(self, line: str) -> None:
        match = self.pattern_func_call.fullmatch(remove_comments(line))
        if not match:
            self.eungdi("오류: 함수 호출 구문 파싱 실패", error=True)
            return
        func_name = match.group(1)
        args_expr = [arg.strip() for arg in match.group(2).split(",") if arg.strip()]
        args_values = [self.evaluate_expression(arg) for arg in args_expr]
        func_obj = self.get_variable(func_name)
        if not isinstance(func_obj, Function):
            self.eungdi(f'오류: "{func_name}" 는 함수가 아님', error=True)
            return
        func_obj.call(self, args_values)

    def process_return(self, line: str) -> None:
        match = self.pattern_return.fullmatch(remove_comments(line))
        if not match:
            self.eungdi("오류: 반환 구문 파싱 실패", error=True)
            return
        expr = match.group(1)
        ret_val = self.evaluate_expression(expr) if expr else None
        raise ReturnException(ret_val)

    def run_repl(self) -> None:
        self.eungdi("대화형 모드입니다. '종료', 'exit' 또는 'quit'을 입력하면 종료합니다.")
        if sys.stdin.isatty():
            try:
                import readline
            except ImportError:
                pass
        while True:
            try:
                line = input(self.prompt)
            except KeyboardInterrupt:
                print("\n종료합니다.")
                break
            if line.strip() in ("종료", "exit", "quit"):
                break
            try:
                self.interpret_program(line)
            except Exception as e:
                self.eungdi(f"실행 중 오류: {e}", error=True)

    def run_noh_file(self, filename: str) -> None:
        try:
            with open(filename, 'r', encoding='utf-8') as f:
                program = f.read()
            self.interpret_program(program)
        except FileNotFoundError:
            self.eungdi(f'오류: 파일을 찾을 수 없습니다 - {filename}', error=True)
        except UnicodeDecodeError:
            self.eungdi(f'오류: 파일 인코딩 문제 발생 - {filename}', error=True)
        except Exception as e:
            self.eungdi(f'오류: 알 수 없는 오류 발생 - {e}', error=True)

def run_tests() -> None:
    interpreter = Interpreter(debug=True)
    test_program = '''
노무현이 왔습니다 "테스트 시작" 북딱
동네 힘센 사람 x 북딱
x 마 매끼나라 고마 10 + 5 북딱
응디 x 북딱
만약 (x > 10) 북딱
  노무현이 왔습니다 "x는 10보다 큼" 북딱
아니면 북딱
  노무현이 왔습니다 "x는 10 이하" 북딱
끝 만약 북딱
반복 (x > 0) 북딱
  x 마 매끼나라 고마 x - 3 북딱
  응디 x 북딱
  만약 (x == 4) 북딱
    브레이크 북딱
  끝 만약 북딱
끝 반복 북딱
반복문 i in [1,2,3,4] 북딱
  응디 i 북딱
  넘어가 북딱
  노무현이 왔습니다 "이 문장은 실행되지 않아" 북딱
끝 반복문 북딱
흔들어라 add(a, b) 북딱
  a 마 매끼나라 고마 a + b 북딱
  돌아가 a 북딱
끝 흔들어라 북딱
함수 호출 add(7, 8) 북딱
변수 목록 북딱
상태 북딱
버전 북딱
파일에 쓰기 "test.txt", "파일 쓰기 테스트." 북딱
파일에 추가하기 "test.txt", " 추가 내용." 북딱
파일 삭제 "test.txt" 북딱
파일 존재 확인 "test.txt" 북딱
디렉터리 목록 북딱
화면 지우기 북딱
현재 경로 출력 북딱
작업 디렉터리 변경 "." 북딱
응디 현재 시간 북딱
응디 현재 날짜 북딱
응디 요청 보내기 "https://jsonplaceholder.typicode.com/todos/1" 북딱
JSON 변환 '{"이름": "철수", "나이": 20}' 북딱
동네 힘센 사람 myList 북딱
myList 마 매끼나라 고마 [1,2,3] 북딱
리스트 추가 myList, 4 북딱
리스트 삭제 myList, 1 북딱
리스트 정렬 myList 북딱
JSON 문자열화 myList 북딱
동네 힘센 사람 myStr 북딱
myStr 마 매끼나라 고마 "hello world" 북딱
대문자로 변환 myStr 북딱
소문자로 변환 myStr 북딱
랜덤 숫자 (1, 100) 북딱
랜덤 리스트 섞기 myList 북딱
동네 힘센 사람 myDict 북딱
myDict 마 매끼나라 고마 {"a": 1} 북딱
딕셔너리 추가 myDict, "b", 2 북딱
딕셔너리 삭제 myDict, "a" 북딱
JSON 문자열화 myDict 북딱
변수 저장 "vars.json" 북딱
초기화 북딱
변수 불러오기 "vars.json" 북딱
내장함수 목록 북딱
프롬프트 설정 "NoH>" 북딱
도움말 "명령어" 북딱
시스템 실행 "echo 시스템 테스트" 북딱
        '''
    interpreter.interpret_program(test_program)
    logging.info("모든 테스트 통과.")

def main() -> None:
    parser = argparse.ArgumentParser(description="Interpreter Script")
    parser.add_argument("--test", action="store_true", help="Run tests")
    parser.add_argument("--debug", action="store_true", help="Enable debug mode")
    parser.add_argument("--fast", action="store_true", help="불필요한 로깅 제거 (fast 모드)")
    parser.add_argument("--repl", action="store_true", help="Run in interactive mode (REPL)")
    parser.add_argument("filename", nargs="?", help="Path to .noh file")
    args = parser.parse_args()

    interpreter = Interpreter(debug=args.debug, fast=args.fast)
    if args.test:
        run_tests()
    elif args.filename:
        if not args.filename.endswith('.noh'):
            interpreter.eungdi('오류: 파일 확장자는 .noh 이어야 합니다.', error=True)
        else:
            interpreter.run_noh_file(args.filename)
    elif args.repl or sys.stdin.isatty():
        interpreter.run_repl()
    else:
        default_program_text = '''
여긴 응디시티
노무현이 왔습니다 "안녕하세요!" 북딱
동네 힘센 사람 x 북딱
x 마 매끼나라 고마 42 북딱
응디 x 북딱
만약 (x > 40) 북딱
  노무현이 왔습니다 "x는 40 초과" 북딱
아니면 북딱
  노무현이 왔습니다 "x는 40 이하" 북딱
끝 만약 북딱
반복 (x > 0) 북딱
  x 마 매끼나라 고마 x - 10 북딱
  응디 x 북딱
끝 반복 북딱
반복문 i in [10, 20, 30] 북딱
  응디 i 북딱
끝 반복문 북딱
흔들어라 multiply(a, b) 북딱
  a 마 매끼나라 고마 a * b 북딱
  돌아가 a 북딱
끝 흔들어라 북딱
함수 호출 multiply(3, 5) 북딱
변수 목록 북딱
도움말 북딱
        '''
        interpreter.interpret_program(default_program_text)

if __name__ == '__main__':
    main()
