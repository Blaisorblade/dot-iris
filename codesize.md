# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
32e36b16c26e1df8790014bdd6b5defc055abe56.

```
theories: 911
theories/iris_extra: 1591
theories/Dot: 158
theories/Dot/hkdot: 1627
theories/Dot/semtyp_lemmas: 1544
theories/Dot/typing: 681
theories/Dot/syn: 2857
theories/Dot/examples: 653
theories/Dot/examples/old_typing: 1316
theories/Dot/examples/sem: 1968
theories/Dot/examples/sem/semtyp_lemmas: 427
theories/Dot/examples/stamping: 168
theories/Dot/examples/syn: 1198
theories/Dot/lr: 2145
theories/DSub: 153
theories/DSub/typing: 229
theories/DSub/syn: 571
theories/DSub/lr: 588
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 10207
Examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5730
Preliminaries + DOT + examples (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 15937

Preliminaries (. iris_extra pure_program_logic): 2822

DOT (Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 7385

syntax (syn): 2857
logrel (lr semtyp_lemmas): 3689
model (syntax + logrel) (syn lr semtyp_lemmas): 6546

syntactic typing (w/ fundamental) (. typing): 839

hkdot (hkdot): 1627

examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5730
```
