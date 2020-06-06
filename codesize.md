# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
ad1fd1d9870481ff1120a6c98c0b39e95e1ab4b8.

```
theories: 804
theories/iris_extra: 1560
theories/Dot: 158
theories/Dot/hkdot: 1627
theories/Dot/semtyp_lemmas: 1544
theories/Dot/typing: 676
theories/Dot/syn: 2702
theories/Dot/examples: 651
theories/Dot/examples/old_typing: 1316
theories/Dot/examples/sem: 1968
theories/Dot/examples/sem/semtyp_lemmas: 427
theories/Dot/examples/stamping: 168
theories/Dot/examples/syn: 1198
theories/Dot/lr: 2113
theories/DSub: 153
theories/DSub/typing: 229
theories/DSub/syn: 478
theories/DSub/lr: 588
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 9877
Examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5728
Preliminaries + DOT + examples (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 15605

Preliminaries (. iris_extra pure_program_logic): 2684

DOT (Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 7193

syntax (syn): 2702
logrel (lr semtyp_lemmas): 3657
model (syntax + logrel) (syn lr semtyp_lemmas): 6359

syntactic typing (w/ fundamental) (. typing): 834

hkdot (hkdot): 1627

examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 5728
```
