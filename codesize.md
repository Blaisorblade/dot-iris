# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
92345862f4d8135aa17a30d06a0ccd00ca8614c9.

```
theories: 793
theories/iris_extra: 1648
theories/Dot: 158
theories/Dot/semtyp_lemmas: 953
theories/Dot/typing: 690
theories/Dot/syn: 2562
theories/Dot/examples: 687
theories/Dot/examples/old_typing: 1288
theories/Dot/examples/sem: 1981
theories/Dot/examples/sem/semtyp_lemmas: 265
theories/Dot/examples/stamping: 171
theories/Dot/examples/syn: 1218
theories/Dot/lr: 2040
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 9164
Examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5610
Preliminaries + DOT + examples (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 14774

Preliminaries (. iris_extra pure_program_logic): 2761

DOT (Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 6403

syntax (syn): 2562
logrel (lr semtyp_lemmas): 2993
model (syntax + logrel) (syn lr semtyp_lemmas): 5555

syntactic typing (w/ fundamental) (. typing): 848

hkdot (hkdot): 0

examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5610
```
