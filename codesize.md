# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
9fde3880c352d49eb086e91890e405c0e44fd3df.

```
theories: 1020
theories/iris_extra: 1817
theories/Dot: 178
theories/Dot/hkdot: 652
theories/Dot/semtyp_lemmas: 1986
theories/Dot/stamping: 2531
theories/Dot/typing: 3177
theories/Dot/syn: 2143
theories/Dot/examples: 3990
theories/Dot/lr: 2688
theories/DSub: 153
theories/DSub/typing: 229
theories/DSub/syn: 637
theories/DSub/lr: 590
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/hkdot Dot/semtyp_lemmas Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 20502

Preliminaries (. iris_extra pure_program_logic): 3157

DOT (Dot Dot/hkdot Dot/semtyp_lemmas Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 17345

syntax (syn): 2143
logrel (lr semtyp_lemmas): 4674
model (syntax + logrel) (syn lr semtyp_lemmas): 6817

syntactic typing (w/ stamping & old_fundamental) (. typing stamping): 5886

examples (examples): 3990
```
