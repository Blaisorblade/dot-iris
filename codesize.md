# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
106979e9e223a155ce71b86972cdbd5d0847204c.

```
theories: 793
theories/iris_extra: 1648
theories/Dot: 158
theories/Dot/hkdot: 1635
theories/Dot/semtyp_lemmas: 1259
theories/Dot/typing: 690
theories/Dot/syn: 2562
theories/Dot/examples: 687
theories/Dot/examples/old_typing: 1288
theories/Dot/examples/sem: 1981
theories/Dot/examples/sem/semtyp_lemmas: 265
theories/Dot/examples/stamping: 171
theories/Dot/examples/syn: 1218
theories/Dot/lr: 2040
theories/DSub: 148
theories/DSub/typing: 229
theories/DSub/syn: 448
theories/DSub/lr: 579
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 9470
Examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5610
Preliminaries + DOT + examples (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 15080

Preliminaries (. iris_extra pure_program_logic): 2761

DOT (Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 6709

syntax (syn): 2562
logrel (lr semtyp_lemmas): 3299
model (syntax + logrel) (syn lr semtyp_lemmas): 5861

syntactic typing (w/ fundamental) (. typing): 848

hkdot (hkdot): 1635

examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5610
```
