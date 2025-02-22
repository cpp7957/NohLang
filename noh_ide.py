import tkinter as tk
from tkinter import scrolledtext, filedialog, messagebox
import sys
import io
import logging
import re
import os
import subprocess

# noh_interpreter.py에 정의된 Interpreter 클래스를 가져온다고 가정합니다.
from noh_interpreter import Interpreter

class NohIDE(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Noh Interpreter IDE")
        self.geometry("1000x800")
        self.configure(bg="#2E2E2E")  # 다크 모드 배경
        self.current_file = None
        self.debug_mode = tk.BooleanVar(value=False)
        
        # 자동 완성 관련 변수
        self.autocomplete_listbox = None
        # Noh 언어의 키워드 목록 (원하는 키워드를 추가하세요)
        self.noh_keywords = [
            "노무현이 왔습니다", "동네 힘센 사람", "마 매끼나라 고마", "응디", "방독면 챙기십쇼",
            "지금까지 뭐했노", "변수 목록 북딱", "변수 삭제", "만약", "아니면", "끝 만약 북딱",
            "반복", "끝 반복 북딱", "반복문", "끝 반복문 북딱", "브레이크 북딱", "넘어가 북딱",
            "흔들어라", "끝 흔들어라 북딱", "함수 호출", "돌아가", "상태 북딱", "버전 북딱",
            "파일에 쓰기", "파일에 추가하기", "파일 삭제", "파일 존재 확인", "디렉터리 목록 북딱",
            "응디 현재 시간 북딱", "응디 현재 날짜 북딱", "응디 요청 보내기",
            "JSON 변환", "JSON 문자열화",
            "리스트 추가", "리스트 삭제", "리스트 정렬",
            "대문자로 변환", "소문자로 변환",
            "랜덤 숫자", "랜덤 리스트 섞기",
            "환경 변수 출력", "환경 변수 설정",
            "거듭제곱", "제곱근", "로그",
            "변수 저장", "변수 불러오기",
            "종료", "프롬프트 설정", "도움말",
            "화면 지우기", "현재 경로 출력", "작업 디렉터리 변경"
        ]
        
        # 메뉴바 생성
        self.create_menu()
        
        # PanedWindow를 사용해 에디터, 출력창, 터미널을 수직으로 분할
        self.paned_window = tk.PanedWindow(self, orient=tk.VERTICAL, bg="#2E2E2E")
        self.paned_window.pack(expand=True, fill=tk.BOTH)
        
        # 에디터 영역 (ScrolledText)
        self.editor = scrolledtext.ScrolledText(self.paned_window, wrap=tk.WORD, font=("Consolas", 14),
                                                bg="#1E1E1E", fg="white", insertbackground="white", padx=10, pady=10)
        self.editor.bind("<Tab>", self.handle_tab)
        self.editor.bind("<KeyRelease>", self.on_key_release)
        self.paned_window.add(self.editor, stretch="always")
        
        # 실행 결과 출력 영역 (ScrolledText)
        self.output = scrolledtext.ScrolledText(self.paned_window, wrap=tk.WORD, font=("Consolas", 12),
                                                bg="#252525", fg="lightgreen", state=tk.DISABLED, height=12, padx=10, pady=10)
        self.paned_window.add(self.output, stretch="always")
        
        # 하단 프레임: 버튼과 터미널 영역을 포함
        self.bottom_frame = tk.Frame(self, bg="#2E2E2E")
        self.bottom_frame.pack(fill=tk.BOTH, expand=False)
        
        # 버튼 프레임 (실행 버튼, 디버그 체크박스)
        self.button_frame = tk.Frame(self.bottom_frame, bg="#2E2E2E")
        self.button_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.run_button = tk.Button(self.button_frame, text="▶ Run", command=self.run_code,
                                    font=("Arial", 12, "bold"), bg="#4CAF50", fg="white", padx=20, pady=5)
        self.run_button.pack(side=tk.LEFT, padx=10)
        
        self.debug_checkbox = tk.Checkbutton(self.button_frame, text="디버그 모드", variable=self.debug_mode,
                                             font=("Arial", 10), bg="#2E2E2E", fg="white", selectcolor="#444")
        self.debug_checkbox.pack(side=tk.LEFT, padx=10)
        
        # 터미널 영역
        self.terminal_frame = tk.Frame(self.bottom_frame, bg="#2E2E2E")
        self.terminal_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0,10))
        # grid 레이아웃으로 터미널 영역 구성
        self.terminal_frame.rowconfigure(0, weight=1)
        self.terminal_frame.columnconfigure(0, weight=1)
        self.terminal_frame.columnconfigure(1, weight=3)
        
        # 터미널 출력 영역
        self.terminal_output = scrolledtext.ScrolledText(self.terminal_frame, wrap=tk.WORD, font=("Consolas", 12),
                                                         bg="#1E1E1E", fg="lightgray", state=tk.DISABLED, padx=10, pady=10)
        self.terminal_output.grid(row=0, column=0, columnspan=2, sticky="nsew")
        
        # 터미널 입력 영역: "Command:" 라벨과 입력창
        self.terminal_label = tk.Label(self.terminal_frame, text="Command:", bg="#2E2E2E", fg="white", font=("Consolas", 12))
        self.terminal_label.grid(row=1, column=0, sticky="w", padx=10, pady=(5,5))
        self.terminal_entry = tk.Entry(self.terminal_frame, font=("Consolas", 12), bg="#555555", fg="white",
                                       insertbackground="white", relief=tk.SOLID, bd=2)
        self.terminal_entry.grid(row=1, column=1, sticky="ew", padx=10, pady=(5,10))
        self.terminal_entry.bind("<Return>", self.execute_terminal_command)
        
        # 상태바 (현재 파일 정보 표시)
        self.status_bar = tk.Label(self, text="No file opened", bd=1, relief=tk.SUNKEN, anchor=tk.W,
                                   bg="#2E2E2E", fg="white")
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 인터프리터 인스턴스 (생성은 run_code()에서)
        self.interpreter = None

    def create_menu(self):
        menubar = tk.Menu(self, bg="#2E2E2E", fg="white")
        
        file_menu = tk.Menu(menubar, tearoff=0, bg="#2E2E2E", fg="white")
        file_menu.add_command(label="New", command=self.new_file)
        file_menu.add_command(label="Open...", command=self.open_file)
        file_menu.add_command(label="Save", command=self.save_file)
        file_menu.add_command(label="Save As...", command=self.save_as_file)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.exit_app)
        menubar.add_cascade(label="File", menu=file_menu)
        
        run_menu = tk.Menu(menubar, tearoff=0, bg="#2E2E2E", fg="white")
        run_menu.add_command(label="Run", command=self.run_code)
        menubar.add_cascade(label="Run", menu=run_menu)
        
        help_menu = tk.Menu(menubar, tearoff=0, bg="#2E2E2E", fg="white")
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)
        
        self.config(menu=menubar)
    
    def new_file(self):
        if self.confirm_discard_changes():
            self.editor.delete("1.0", tk.END)
            self.current_file = None
            self.status_bar.config(text="New File")
    
    def open_file(self):
        if not self.confirm_discard_changes():
            return
        file_path = filedialog.askopenfilename(filetypes=[("Noh Files", "*.noh"), ("All Files", "*.*")])
        if file_path:
            try:
                with open(file_path, "r", encoding="utf-8") as f:
                    content = f.read()
                self.editor.delete("1.0", tk.END)
                self.editor.insert(tk.END, content)
                self.current_file = file_path
                self.status_bar.config(text=f"Opened: {os.path.basename(file_path)}")
            except Exception as e:
                messagebox.showerror("Open File Error", str(e))
    
    def save_file(self):
        if self.current_file:
            try:
                with open(self.current_file, "w", encoding="utf-8") as f:
                    f.write(self.editor.get("1.0", tk.END))
                self.status_bar.config(text=f"Saved: {os.path.basename(self.current_file)}")
            except Exception as e:
                messagebox.showerror("Save File Error", str(e))
        else:
            self.save_as_file()
    
    def save_as_file(self):
        file_path = filedialog.asksaveasfilename(defaultextension=".noh",
                                                 filetypes=[("Noh Files", "*.noh"), ("All Files", "*.*")])
        if file_path:
            try:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(self.editor.get("1.0", tk.END))
                self.current_file = file_path
                self.status_bar.config(text=f"Saved: {os.path.basename(file_path)}")
            except Exception as e:
                messagebox.showerror("Save File Error", str(e))
    
    def exit_app(self):
        if self.confirm_discard_changes():
            self.destroy()
    
    def confirm_discard_changes(self):
        return True
    
    def show_about(self):
        messagebox.showinfo("About", "Noh Interpreter IDE\nVersion 1.0\n\nCreated by cpp7957")
    
    def handle_tab(self, event):
        self.editor.insert("insert", "  ")
        return "break"
    
    def on_key_release(self, event):
        # 자동 완성을 위해 현재 단어를 가져옵니다.
        cursor_index = self.editor.index("insert")
        word_start = self.editor.index("insert wordstart")
        current_word = self.editor.get(word_start, cursor_index)
        # 현재 단어가 없으면 자동완성 목록 제거
        if not current_word:
            if self.autocomplete_listbox:
                self.autocomplete_listbox.destroy()
                self.autocomplete_listbox = None
            return
        
        # 키워드 목록에서 현재 단어로 시작하는 키워드 찾기 (대소문자 구분 없이)
        suggestions = [kw for kw in self.noh_keywords if kw.startswith(current_word)]
        if suggestions:
            if not self.autocomplete_listbox:
                self.autocomplete_listbox = tk.Listbox(self.editor, font=("Consolas", 12), bg="#1E1E1E", fg="white")
                self.autocomplete_listbox.bind("<<ListboxSelect>>", self.on_autocomplete_select)
            else:
                self.autocomplete_listbox.delete(0, tk.END)
            for s in suggestions:
                self.autocomplete_listbox.insert(tk.END, s)
            # 현재 커서 위치의 좌표를 가져와 Listbox를 배치
            bbox = self.editor.bbox("insert")
            if bbox:
                x, y, width, height = bbox
                self.autocomplete_listbox.place(x=x, y=y+height)
        else:
            if self.autocomplete_listbox:
                self.autocomplete_listbox.destroy()
                self.autocomplete_listbox = None
    
    def on_autocomplete_select(self, event):
        if self.autocomplete_listbox:
            selection = self.autocomplete_listbox.curselection()
            if selection:
                chosen = self.autocomplete_listbox.get(selection[0])
                cursor_index = self.editor.index("insert")
                word_start = self.editor.index("insert wordstart")
                current_word = self.editor.get(word_start, cursor_index)
                remainder = chosen[len(current_word):]
                self.editor.insert(cursor_index, remainder)
            self.autocomplete_listbox.destroy()
            self.autocomplete_listbox = None
    
    def run_code(self):
        code = self.editor.get("1.0", tk.END).strip()
        debug_flag = self.debug_mode.get()
        self.interpreter = Interpreter(debug=debug_flag)
        
        old_stdout = sys.stdout
        old_stderr = sys.stderr
        sys.stdout = io.StringIO()
        sys.stderr = io.StringIO()
        
        log_stream = io.StringIO()
        log_handler = logging.StreamHandler(log_stream)
        log_handler.setFormatter(logging.Formatter('%(message)s'))
        logger = logging.getLogger()
        logger.setLevel(logging.DEBUG)
        logger.addHandler(log_handler)
        
        try:
            self.interpreter.interpret_program(code)
            output_text = sys.stdout.getvalue() + sys.stderr.getvalue() + log_stream.getvalue()
        except Exception as e:
            output_text = f"실행 중 오류: {e}"
        finally:
            sys.stdout = old_stdout
            sys.stderr = old_stderr
            logger.removeHandler(log_handler)
        
        self.output.config(state=tk.NORMAL)
        self.output.delete("1.0", tk.END)
        self.insert_colored_text(output_text)
        self.output.config(state=tk.DISABLED)
    
    def insert_colored_text(self, text):
        """ ANSI 색상 코드를 해석하여 Tkinter Text 위젯에 컬러 텍스트를 삽입하는 함수 """
        ansi_colors = {
            "30": "black", "31": "red", "32": "green", "33": "yellow",
            "34": "blue", "35": "magenta", "36": "cyan", "37": "white",
            "90": "gray", "91": "light red", "92": "light green",
            "93": "light yellow", "94": "light blue", "95": "light magenta",
            "96": "light cyan", "97": "light white"
        }
        ansi_escape = re.compile(r'\x1B\[(\d{1,2})m')
        last_end = 0
        current_tag = None
        for match in ansi_escape.finditer(text):
            start, end = match.span()
            color_code = match.group(1)
            if start > last_end:
                self.output.insert(tk.END, text[last_end:start], current_tag)
            color = ansi_colors.get(color_code, None)
            if color:
                current_tag = f"color_{color}"
                self.output.tag_configure(current_tag, foreground=color)
            last_end = end
        if last_end < len(text):
            self.output.insert(tk.END, text[last_end:], current_tag)
    
    def execute_terminal_command(self, event=None):
        cmd = self.terminal_entry.get().strip()
        if cmd:
            self.terminal_output.config(state=tk.NORMAL)
            self.terminal_output.insert(tk.END, f"> {cmd}\n")
            self.terminal_entry.delete(0, tk.END)
            try:
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                output = result.stdout
                error = result.stderr
                if output:
                    self.terminal_output.insert(tk.END, output)
                if error:
                    self.terminal_output.insert(tk.END, error)
            except Exception as e:
                self.terminal_output.insert(tk.END, f"실행 오류: {e}\n")
            self.terminal_output.config(state=tk.DISABLED)
            self.terminal_output.see(tk.END)
        return "break"
    
    def create_menu(self):
        menubar = tk.Menu(self, bg="#2E2E2E", fg="white")
        file_menu = tk.Menu(menubar, tearoff=0, bg="#2E2E2E", fg="white")
        file_menu.add_command(label="New", command=self.new_file)
        file_menu.add_command(label="Open...", command=self.open_file)
        file_menu.add_command(label="Save", command=self.save_file)
        file_menu.add_command(label="Save As...", command=self.save_as_file)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.exit_app)
        menubar.add_cascade(label="File", menu=file_menu)
        
        run_menu = tk.Menu(menubar, tearoff=0, bg="#2E2E2E", fg="white")
        run_menu.add_command(label="Run", command=self.run_code)
        menubar.add_cascade(label="Run", menu=run_menu)
        
        help_menu = tk.Menu(menubar, tearoff=0, bg="#2E2E2E", fg="white")
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)
        
        self.config(menu=menubar)
    
    def update_status(self, text):
        self.status_bar.config(text=text)

if __name__ == "__main__":
    app = NohIDE()
    app.mainloop()
