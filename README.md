# memento-proof

Coq mechanization of Section 3 and Appendices F–H of K. Cho, S. Jeon,
A. Raad and J. Kang, *Memento: A Framework for Detectable Recoverability in
Persistent Memory*, PLDI 2023 (Proc. ACM Program. Lang. 7, PLDI, Article 118).
Numbers refer to the full version, whose Appendix H contains the proof.

## Build

Requires Coq 8.15.

```sh
git submodule update --init
make
```

`scripts/check.sh` rebuilds from scratch, checks that no `admit` remains, and
lists the axioms of the main theorems.

## Paper and code

| Paper | Coq | File |
|---|---|---|
| Fig. 16, syntax | `Val.t`, `Expr`, `Stmt`, `Program` | `src/lang/Syntax.v` |
| Fig. 17, states | `VRegMap.t`, `Cont.t`, `TState.t`, `Mmts.t`, `Thread.t`, `Machine.t` | `src/lang/Semantics.v` |
| Fig. 18, machine | `Machine.init`, `Machine.normal`, `Machine.crash`, `Machine.step` | `src/lang/Semantics.v` |
| Fig. 19, memory | `Mem.step` | `src/lang/Semantics.v` |
| Figs. 20–21, thread transitions | `Thread.step` | `src/lang/Semantics.v` |
| Fig. 22, type system | `EnvType.ro_judge`, `EnvType.rw_judge`, `TypeSystem.judge`, `TypeSystem.prog_judge` | `src/type/Env.v` |
| Fig. 23 | `trace_refine` (`~`) | `src/proof/Common.v` |
| Theorem 3.1 | `detectability` | `src/proof/Detectability.v` |
| Definition 3.2 | `DR_main` | `src/proof/DR.v` |
| Lemma 3.3 | `DR_RW_main` | `src/proof/DRRW.v` |
| Theorem 3.4 | `erase`, `erasure` | `src/erase/Erasure.v` |
| Theorem 3.4, erased programs | `EStmt`, `EThread.step`, `EMachine.normal`, `EB` | `src/erase/Erased.v` |
| Observation 1, Lemma 4.1 | none, implementation level | |
| H.1, H.2 | `Thread.rtc`, `Thread.tc`, `Machine.rtc` | `src/lang/Semantics.v` |
| H.3 | `seq_sc` (`++₁`) | `src/lang/Semantics.v` |
| H.4 | `seq_lifting` | `src/proof/Lifting.v` |
| H.5 | `lift_cont` | `src/proof/Lifting.v` |
| H.6 | `mmt_id_exp` | `src/proof/Common.v` |
| H.7 | `lift_mmt` | `src/proof/Lifting.v` |
| H.8 | `seq_cases` | `src/proof/Lifting.v` |
| H.9 | `Thread.step_base_cont` | `src/lang/Semantics.v` |
| H.10 | `loop_cases_H10` | `src/proof/Lifting.v` |
| H.11 | `first_loop_iter_H11` | `src/proof/Lifting.v` |
| H.12 | `last_loop_iter_H12` | `src/proof/Lifting.v` |
| H.13 | `chkpt_fn_cases_H13` | `src/proof/Lifting.v` |
| H.14 | `Thread.step_time_mon` | `src/lang/Semantics.v` |
| H.15 | `TypeSystem.judge_dom` | `src/type/Env.v` |
| H.16 | `STOP` | `src/proof/Common.v` |
| H.17 | `stop_no_step` | `src/proof/Common.v` |
| H.18 | `BE`, `B` | `src/proof/Detectability.v` |
| H.19 | `trace_refine` (`~`) | `src/proof/Common.v` |
| H.20 | `crash_free_interleaving` | `src/proof/Detectability.v` |
| H.21 | `interleaving` | `src/proof/Detectability.v` |
| H.21, transitions with crashes | `Thread.stepE`, `Thread.rtcE` | `src/lang/Semantics.v` |
| H.22 | `DR` | `src/proof/DR.v` |
| H.23 | `DR_RW` | `src/proof/DRRW.v` |
| H.24 | `detectability` | `src/proof/Detectability.v` |
| H.25 | `read_only_statements` | `src/proof/Lifting.v` |
| H.26 | `DR_RW_ind` | `src/proof/DRRW.v` |
| H.26, case loop-simple | `DR_loop_simple` | `src/proof/LoopSimple.v` |
| Example, transaction | `transaction_atomic` | `src/examples/transaction.v` |

The proofs use only the standard axioms `functional_extensionality_dep`,
`constructive_indefinite_description` and `classic`.
