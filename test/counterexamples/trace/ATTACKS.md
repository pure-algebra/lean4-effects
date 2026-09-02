# Trace attacks

Witnesses live in `EffectsTest/Counterexamples/Trace/Around.lean`; rows in
`test/counterexamples/REGISTER.md`.

## EF-TRACE-CE-001 — a tracing handler is `mapHom` of a lift

BROKE: the claim that tracing is a monad-homomorphism transport of the plain
handler. WITNESS: `mapHom_logs_nothing`; the lifted handler runs `incr` to 42
with an empty log. CLASS: representation. FIXED-BY: `Family.Service.traced` is
an around-wrapper; its law is `interpret_traced_fst`, not `interpret_mapHom`.

## EF-TRACE-CE-002 — answers are redundant

BROKE: "operation order plus outcome determines the run". WITNESS:
`answers_separate_what_ops_do_not`; services answering 41 and 5 give equal
operation-only projections and equal outcomes. CLASS: mask design. FIXED-BY:
`Mask.m1` keeps `answer` and `failed` rows.

## EF-TRACE-CE-003 — agreement without a mask

BROKE: comparing unprojected traces as the agreement judgment. WITNESS:
`agreement_is_per_mask`; two traces agree under `m1`, differ raw and under
`m2`. CLASS: claim scope. FIXED-BY: every agreement names its mask;
`agree_of_agree_m2` is the only refinement direction.
