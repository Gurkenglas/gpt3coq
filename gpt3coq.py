import argparse

parser = argparse.ArgumentParser(description='Make GPT-3 complete Coq files.')
parser.add_argument('--top_p', dest='top_p', type=float, default=0.9)
parser.add_argument('file', type=str, help='the file to complete')

args = parser.parse_args()
print(args.top_p)
print(args.file)

import sys, pexpect

coqtop = pexpect.spawn("coqtop -load-vernac-source " + args.file)

coqtop.expect("\n\w* < ")
if coqtop.before.find("Error".encode()) > -1:
  sys.stderr.write("Module didn't compile.\n")

with open (args.file, "r") as promptfile:
  prompt = promptfile.read()

import openai

while(True):
  prompt = prompt[-3000:]
  line = openai.Completion.create(model="engine", prompt=prompt, stop=".", top_p=args.top_p, max_tokens=50)['choices'][0]['text'] + "."
  sys.stderr.write("Trying: " + line + "\n")
  coqtop.sendline(line)
  coqtop.expect("\n\w* < ")
  sys.stderr.write("Reply: " + coqtop.before.decode() + "\n")
  if coqtop.before.find("Error".encode()) == -1:
    sys.stdout.write(line)
    prompt += line
