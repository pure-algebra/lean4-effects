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

## EF-TRACE-CE-004 — a defect rendered as a failure

BROKE: the v0.5.0 alphabet's claim that `success`, `failure` and `interrupted`
name every way a program, a region body or a finalizer can end, so a host
defect (an rc.112 `Die`) may be recorded as a `failure` carrying the same
payload. WITNESS: `a_defect_rendered_as_a_failure`; `squashEvent`, the
endomorphism that rewrites `defect e` to `failure e` in every outcome an event
carries, sends the `done (.defect "boom")` trace and the `done (.failure
"boom")` trace to one trace, while the two differ under `outcomeOnly`, `m1`
and `m2` alike — a mask decides on an event's kind and never on the outcome it
carries, so no projection recovers what the collapse loses. The same collapse
is observable on the host: the rc.112 tracer rendered a die as
`{"failure":[]}`, byte-identical to a failure of unit. CLASS: alphabet
completeness. FIXED-BY: `Outcome.defect` is a constructor of its own (v0.6.0),
and every consumer that pattern-matches an outcome gives it its own arm.
