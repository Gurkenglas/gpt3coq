import sys, pexpect

coqtop = pexpect.spawn("coqtop -load-vernac-source " + sys.argv[1])

coqtop.expect("\n\w* < ")
if coqtop.before.find("Error".encode()) == -1:
  sys.stderr.write("module didn't compile")

with open (sys.argv[1], "r") as promptfile:
  prompt = promptfile.read()

import openai

while(True):
  line = repr(openai.Completion.create(model="engine", prompt=prompt, stop=".", temperature=0, max_tokens=300))
  coqtop.sendline(line)
  coqtop.expect("\n\w* < ")
  if coqtop.before.find("Error".encode()) == -1:
    print(line)
    prompt += line + "\n"
  else:
    sys.stderr.write("Tried: " + line)
