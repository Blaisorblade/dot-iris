# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
64bf2070edbd58c0ea8981e5728fa4a49eb123bf.

```
theories: 1018
theories/iris_extra: 1764
theories/Dot: 176
theories/Dot/semtyp_lemmas: 1238
theories/Dot/stamping: 2428
theories/Dot/typing: 2724
theories/Dot/syn: 2141
theories/Dot/examples: 4051
theories/Dot/lr: 1460
theories/pure_program_logic: 316

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 17316

Preliminaries (. iris_extra pure_program_logic): 3098

DOT (Dot Dot/semtyp_lemmas Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 14218

syntax (syn): 2141
logrel (lr semtyp_lemmas): 2698
model (syntax + logrel) (syn lr semtyp_lemmas): 4839

syntactic typing (w/ stamping & fundamental) (. typing stamping): 5328

examples (examples): 4051
```
