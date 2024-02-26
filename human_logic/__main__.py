import cmd
import re

import instructor

import openai
from openai import OpenAI, APITimeoutError
from pydantic import BaseModel, ValidationError
from retry import retry

from human_logic.fol_solver import check_fol_proof


OPENAI_CLIENT = None
MODEL = "gpt-4-0125-preview" # 4 Turbo
DEBUG = False

def init_openai():
    if DEBUG:
        openai.log = "debug"
    global OPENAI_CLIENT
    OPENAI_CLIENT = instructor.patch(OpenAI(timeout=30.0))


class LogicLine(BaseModel):
    """
    Represents a line of logic with its corresponding comment and FOL expression.
    """
    comment: str
    fol: str

class LogicLineWrapper(BaseModel):
    text: str
    logic_line: LogicLine | None
    is_conclusion: bool

class LogicLines(BaseModel):
    lines: list[LogicLine]

def logic_line_prompt(text: str, context_lines: list[LogicLineWrapper]):
    context = "\n".join([line.logic_line.fol for line in context_lines if line.logic_line])
    return f"""
```
{text}
```
Convert the above into a logic line.
A logic line these parts:
* comment: text description
* fol: First-Order Logic notation, symbols ∀ ¬ ∃ ∧ ∨ → ↔, example:
    * ∀ x P(x)
    * ∀ x (Man(x) → Mortal(x))
    * Mortal(Socrates)

# Context
Be consistent with the names in the previous steps.
```
{context}
```
"""

@retry((ValidationError, APITimeoutError), tries=3, delay=1)
def generate_logic_lines(
    text: str,
    context_lines: list[LogicLine]
) -> LogicLine | None:
    if not text.strip():
        return None
    prompt = logic_line_prompt(text, context_lines)
    response = OPENAI_CLIENT.chat.completions.create(
        model=MODEL,
        response_model=LogicLine,
        temperature = 0.2,
        messages=[
            {"role": "user", "content": prompt},
        ]
    )
    return response

def format_fol(line: LogicLine):
    text = line.fol
    text = text.replace("\f", r'\f')
    text = text.replace("\r", r'\r')
    text = text.replace("\t", r'\t')
    text = text.replace("\n", r'\n')
    text = text.replace(r'\forall', '∀')
    text = text.replace(r'\neg', '¬')
    text = text.replace(r'\exists', '∃')
    text = text.replace(r'\land', '∧')
    text = text.replace(r'\lor', '∨')
    text = text.replace(r'\to', '→')
    text = text.replace(r'\rightarrow', '→')
    text = text.replace(r'\leftrightarrow', '↔')
    text = text.strip()
    return text


class Lang(cmd.Cmd):
    intro = """Welcome to the FOL Assistant shell.
Using OpenAI key in OPENAI_API_KEY.
Type help or ? to list commands.
"""
    prompt = 'FOL> '
    file = None
    lines: list[LogicLineWrapper] = []
    def do_q(self, arg):
        'Quit: q'
        print('Exiting')
        return True
    
    def default(self, line: str):
        if line == 'EOF':
            print()
            return True
        match = re.match(r'^([cC])?(\d+)?\b(.*)', line)
        if match:
            is_conclusion, number, text = match.groups()
            is_conclusion = bool(is_conclusion)
            if is_conclusion:
                self.lines = [line for line in self.lines if not line.is_conclusion]
            if is_conclusion or not number:
                zero_index = len(self.lines)
            else:
                zero_index = int(number) - 1
            context_lines = self.lines
            if zero_index >= 0 and zero_index < len(self.lines):
                context_lines = self.lines[:zero_index] + self.lines[zero_index+1:]
            
            gen_line = LogicLineWrapper(text=text.strip(), z3_line=None, logic_line=None, is_conclusion=is_conclusion)
            
            if number == '0':
                self.lines = [gen_line] + self.lines
            else:
               
                if zero_index < len(self.lines):
                    self.lines = self.lines[:zero_index] + [gen_line] + self.lines[zero_index+1:]
                else:
                    self.lines.append(gen_line)
            self.lines = [line for line in self.lines if line and line.text]
        else:
            print(f"ERROR Unknown command `{line}`")
        self.do_list()
        if gen_line.text:
            print('Resolving new item...')
            
            gen_line.logic_line = generate_logic_lines(gen_line.text, context_lines)
            if DEBUG:
                print(gen_line.logic_line.json())
            print()
            print("# Text")
            self.do_list("text")
            print()
            print("# FOL")
            self.do_list()
        if self.lines:
            valid, reason = self.check_proof()
            print()
            if valid:
                print("Z3 verified")
            else:
                print("Z3 failed:", reason)
        print()
        return False
    
    def do_list(self, format: str="FOL"):
        """List logic lines as in format (FOL / text, default FOL)"""
        text_format = format == "text"
        for i, line in enumerate(self.lines):
            num_text = i+1
            if line.is_conclusion:
                num_text = 'C'
            if line.logic_line and not text_format:
                print(f"{num_text} " + format_fol(line.logic_line))
            else:
                print(f"{num_text} " + line.text)

    def check_proof(self):
        fol_lines = [
            line.logic_line.fol
            for line in self.lines 
            if line.logic_line and not line.is_conclusion
        ]
        conclusion_fol_lines = [
            line.logic_line.fol
            for line in self.lines 
            if line.logic_line and line.is_conclusion
        ]
        missing = [line for line in self.lines if not line.logic_line]
        for line in missing:
            print(f"WARNING: missing FOL notation for line {line.text}")
        conclusion = None
        if conclusion_fol_lines:
            conclusion = conclusion_fol_lines[0]
        if len(conclusion_fol_lines) > 1:
            print(f"WARNING: More than one conclusion line, only checking first")
        return check_fol_proof(fol_lines, conclusion)

if __name__ == '__main__':
    init_openai()
    Lang().cmdloop()

