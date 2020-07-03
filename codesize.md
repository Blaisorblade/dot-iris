# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
5f2bd7521e4ccb672ab476984dc86ef0ada0ebe4.

```
theories: 793
theories/iris_extra: 1648
theories/Dot: 157
theories/Dot/hkdot: 1635
theories/Dot/semtyp_lemmas: 1253
theories/Dot/typing: 669
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

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 9442
Examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5610
Preliminaries + DOT + examples (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 15052

Preliminaries (. iris_extra pure_program_logic): 2761

DOT (Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 6681

syntax (syn): 2562
logrel (lr semtyp_lemmas): 3293
model (syntax + logrel) (syn lr semtyp_lemmas): 5855

syntactic typing (w/ fundamental) (. typing): 826

hkdot (hkdot): 1635

examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5610
```
