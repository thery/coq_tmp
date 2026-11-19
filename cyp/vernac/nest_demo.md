---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# nest_demo

Let `n : nat`{.var}. We prove `n <= n + 12`{.claim}.

- We have `n <= n + 12 /\ n <= n + 12 + 1`{.claim}.
  - We have `n <= n + 11 /\ n <= n + 11 + 1`{.claim}.
    - We have `n <= n + 10 /\ n <= n + 10 + 1`{.claim}.
      - We have `n <= n + 9 /\ n <= n + 9 + 1`{.claim}.
        - We have `n <= n + 8 /\ n <= n + 8 + 1`{.claim}.
          - We have `n <= n + 7 /\ n <= n + 7 + 1`{.claim}.
            - We have `n <= n + 6 /\ n <= n + 6 + 1`{.claim}.
              - We have `n <= n + 5 /\ n <= n + 5 + 1`{.claim}.
                - We have `n <= n + 4 /\ n <= n + 4 + 1`{.claim}.
                  - We have `n <= n + 3 /\ n <= n + 3 + 1`{.claim}.
                    - We have `n <= n + 2 /\ n <= n + 2 + 1`{.claim}.
                      - We have `n <= n + 1 /\ n <= n + 1 + 1`{.claim}.
                        - We have `n <= n + 0 /\ n <= n + 0 + 1`{.claim}.
