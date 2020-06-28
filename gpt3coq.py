import sys, pexpect

coqtop = pexpect.spawn("coqtop -load-vernac-source " + sys.argv[1])

coqtop.expect("\n\w* < ")
if coqtop.before.find("Error".encode()) > -1:
  sys.stderr.write("Module didn't compile.\n")

with open (sys.argv[1], "r") as promptfile:
  prompt = promptfile.read()

import openai

while(True):
  prompt = prompt[-3000:]
  line = openai.Completion.create(model="engine", prompt=prompt, stop=".", temperature=0, max_tokens=300)['choices'][0]['text']
  coqtop.sendline(line)
  coqtop.expect("\n\w* < ")
  if coqtop.before.find("Error".encode()) == -1:
    sys.stdout.write(line)
    prompt += line
  else:
    sys.stderr.write("Tried: " + line + "\n")
