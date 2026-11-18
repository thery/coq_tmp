---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# nest_demo

Let `n : nat`. We prove `n <= n + 12`.

- We have `n <= n + 12` and `n <= n + 12 + 1`.
  - We have `n <= n + 11` and `n <= n + 11 + 1`.
    - We have `n <= n + 10` and `n <= n + 10 + 1`.
      - We have `n <= n + 9` and `n <= n + 9 + 1`.
        - We have `n <= n + 8` and `n <= n + 8 + 1`.
          - We have `n <= n + 7` and `n <= n + 7 + 1`.
            - We have `n <= n + 6` and `n <= n + 6 + 1`.
              - We have `n <= n + 5` and `n <= n + 5 + 1`.
                - We have `n <= n + 4` and `n <= n + 4 + 1`.
                  - We have `n <= n + 3` and `n <= n + 3 + 1`.
                    - We have `n <= n + 2` and `n <= n + 2 + 1`.
                      - We have `n <= n + 1` and `n <= n + 1 + 1`.
                        - We have `n <= n + 0` and `n <= n + 0 + 1`.
