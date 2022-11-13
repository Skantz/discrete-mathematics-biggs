From mathcomp Require Import ssreflect ssrbool ssrnat div algC.


(* 1.2.1 *)

(* 200 000 000 gives stack overflow *)
Lemma e121a : (5 %| 2000).
Proof.
  replace 2000 with (5 * 400). 2: {auto. }
  unfold "%|".
  by rewrite modnMr.
Defined.

(* How to negate? *)
Lemma e121b : not (5 %| 263).
Proof.
Abort.

Definition e131 := (3 %| 81270) \/ (7 %| 81270).

Definition e132 := (375 %| 200000000)
  -> (375 %| 400000000).

Definition e141 := exists x, (3 * x %| 123456789).

Definition e142_false := exists n m : nat, n * n = 2 * m * m.

Lemma e142 : not (exists n m : nat, n * n = 2 * m * m).
Proof.
  unfold not.
  intros.
  destruct H as [n [m H]].
Abort.