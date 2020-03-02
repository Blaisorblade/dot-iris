# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
2f420144d7f36daa84e97bf2f0c021b3a752c956.

```
theories: 1022
theories/iris_extra: 1327
theories/Dot: 170
theories/Dot/stamping: 2562
theories/Dot/misc_unused: 1434
theories/Dot/typing: 2820
theories/Dot/syn: 2095
theories/Dot/examples: 4193
theories/Dot/lr: 2647
theories/misc_unused: 616
theories/DSub/stamping: 1016
theories/DSub/misc_unused: 75
theories/DSub/typing: 137
theories/DSub/syn: 654
theories/DSub/lr: 219
theories/DSubSyn: 152
theories/DSubSyn/typing: 221
theories/DSubSyn/lr: 521
theories/pure_program_logic: 730

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 2125

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 17566

Preliminaries (. iris_extra pure_program_logic): 3079

DOT (Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 14487

syntax (syn): 2095
logrel (lr): 2647
model (syntax + logrel) (syn lr): 4742

syntactic typing (w/ stamping & fundamental) (. typing stamping): 5552

examples (examples): 4193
```
