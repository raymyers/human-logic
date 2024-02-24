import cmd
import re

class Lang(cmd.Cmd):
    intro = 'Welcome to the FOL Assistant shell. Type help or ? to list commands.\n'
    prompt = 'FOL> '
    file = None
    lines = []
    def do_q(self, arg):
        'Quit: q'
        print('Exiting')
        return True
    
    def default(self, line):
        if line == 'EOF':
            print()
            return True
        match = re.match(r'^(\d+)\b(.*)', line)
        if match:
            number, text = match.groups()
            if int(number) == 0:
                self.lines.insert(0, text)
            else:
                if int(number) - 1 < len(self.lines):
                    self.lines[int(number) - 1] = text
                else:
                    self.lines.append(text)
                self.lines = [line for line in self.lines if line.strip()]
        else:
            print(f"ERROR Unknown command `{line}`")
        self.list_lines()
        return False
    
    def list_lines(self):
        'List lines with numbers'
        for i, line in enumerate(self.lines):
            print(f"{i+1:2} {line}")
if __name__ == '__main__':
    Lang().cmdloop()

