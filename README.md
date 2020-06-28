# gpt3coq
Make GPT-3 complete Coq files.

Feel free to submit Coq files for completion. Ideally, give GPT-3 some examples to work with. GPT-3 will ignore everything but the last 3000 characters in the file when producing completions.

Example usage: python3 gpt3coq.py --top_p 0.9 modal.v 2> modal.log
