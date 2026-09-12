import Init

/-!
# Physical AI: information limits and conditional composition

A standalone, domain-independent mathematical kernel.

Purpose
-------
Local correctness claims do not, by themselves, justify their composition.
This file studies the information and contract conditions under which such a
composition is justified. Its statements concern abstract predicates and
relations, not an operational design for a physical system.

Main results
------------
1. `information_loss_impossibility`: a summary that identifies two states with
   different admissibility cannot support both sound and complete decisions.
2. `exact_decisions_iff_separation`: preserving the relevant distinctions is
   necessary and sufficient for an exact *logical predicate* on summaries.
3. `postprocessing_cannot_repair_loss`: processing an unchanged summary cannot
   recover a distinction that it has already erased.
4. `pipeline_information_loss_impossibility`: the same limit persists from any
   intermediate stage through any finite number of heterogeneous postprocessing
   stages.
5. `summary_transferable_iff_compatible` and the `summary_based_*` results:
   a necessary-and-sufficient summary interface condition connects local
   guarantees to finite-window contract composition.
6. `arbitrary_length_composition` and `all_prefixes_preserve_invariant`, plus
   their bounded counterparts: locally established contracts compose over the
   stated finite length with explicit compatibility and invariant hypotheses.
7. `substitution_preserves_composition` and `simulation_preserves_invariant`:
   behavioral refinement, including a different internal state space, preserves
   the stated guarantees when its simulation obligations are established.
8. `finite_progress` and `bounded_progress`: progress is a separate result,
   requiring explicit local
   existence hypotheses rather than following from correctness alone.

The examples use only anonymous finite mathematical states. No correspondence
between these states and an application architecture is supplied.

Interpretation boundary
-----------------------
* `admissible` is a mathematical predicate supplied to a theorem. This file does
  not compute that predicate for a real system or establish its physical meaning.
* A contract is a condition on a transition relation, not a flag that a system
  may declare true. Local correctness is a hypothesis to discharge separately.
* Invariant results concern the states/transitions represented by the chosen
  model. Continuous behavior, interference, and actual implementation fidelity
  are not inferred from a boundary-state model.
* The length quantifier is mathematical compositionality. It is not a bound on
  execution time, verification cost, memory use, reliability, or deployment size.
* Sound refusal is possible with incomplete information. The impossibility
  concerns soundness AND completeness, not soundness alone.
* Finite progress is existence of finite executions under additional hypotheses.
  It does not establish fairness or eventual completion of an arbitrary run.
* These are general logical results; no claim of a unique implementation,
  technical novelty, or unconditional real-world safety follows from them.

Verification
------------
Dependency: Lean 4's `Init` only; no Mathlib or additional project files.
Validated with: Lean (version 4.33.1, x86_64-w64-windows-gnu, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release).
Validation command (repository root): lean PhysicalAIPublicComposition.lean
Compiler result: exit code 0; no errors and no warnings.
Principal axiom audit: the listed declarations have no `sorryAx`, `Classical.choice`,
`Quot.sound`, or added-axiom dependency. The finite-window conditional examples
use standard `propext` transitively; the core information and composition
results are otherwise axiom-free.

日本語要旨
----------
局所的な正しさだけでは、接続後の正しさは自動的には導けない。
必要な区別が情報表現で失われる場合の限界と、明示した抽象条件の下で
保証を任意の有限長へ合成できることを記述する。情報表現から次の前提へ
保証を渡せる条件の必要十分性も示す。具体的な実現方法は扱わない。
本ファイルは実機の安全性・処理性能・秘密保持を証明するものではない。
-/

set_option autoImplicit false

namespace PhysicalAIPublicComposition

universe u v w z

/-! ## 1. Information limits -/

section Information

variable {State : Type u} {Summary : Type v} {Action : Type w}

/-- No admitted state/action pair is outside the specified predicate. -/
def DecisionSound
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (accept : Summary → Action → Prop) : Prop :=
  ∀ s a, accept (view s) a → admissible s a

/-- Every pair satisfying the specified predicate is admitted. -/
def DecisionComplete
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (accept : Summary → Action → Prop) : Prop :=
  ∀ s a, admissible s a → accept (view s) a

/-- Exactness is a two-sided requirement, not merely absence of false positives. -/
def DecisionExact
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (accept : Summary → Action → Prop) : Prop :=
  DecisionSound view admissible accept ∧
  DecisionComplete view admissible accept

/-- Equal summaries preserve all distinctions relevant to this predicate. -/
def Separates
    (view : State → Summary)
    (admissible : State → Action → Prop) : Prop :=
  ∀ s t, view s = view t → ∀ a, (admissible s a ↔ admissible t a)

/-- If a summary also represents an inadmissible state, a sound decision must
    refuse that summary for the specified action. -/
theorem information_loss_forces_refusal
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (accept : Summary → Action → Prop)
    (s t : State) (a : Action)
    (same : view s = view t)
    (bad : ¬ admissible t a)
    (sound : DecisionSound view admissible accept) :
    ¬ accept (view s) a := by
  intro admitted
  have admittedAtT : accept (view t) a := same ▸ admitted
  exact bad (sound t a admittedAtT)

/-- Information loss makes simultaneous soundness and completeness impossible.
    No claim is made that soundness alone is impossible. -/
theorem information_loss_impossibility
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (s t : State) (a : Action)
    (same : view s = view t)
    (good : admissible s a)
    (bad : ¬ admissible t a) :
    ¬ ∃ accept : Summary → Action → Prop,
        DecisionExact view admissible accept := by
  intro candidate
  cases candidate with
  | intro accept exactness =>
    have refuse := information_loss_forces_refusal
      view admissible accept s t a same bad exactness.1
    exact refuse (exactness.2 s a good)

/-- An exact summary-based predicate cannot identify opposite verdicts. -/
theorem exact_decisions_preserve_distinctions
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (accept : Summary → Action → Prop)
    (exactness : DecisionExact view admissible accept) :
    Separates view admissible := by
  intro s t same a
  constructor
  · intro good
    have admitted : accept (view s) a := exactness.2 s a good
    have transferred : accept (view t) a := same ▸ admitted
    exact exactness.1 t a transferred
  · intro good
    have admitted : accept (view t) a := exactness.2 t a good
    have transferred : accept (view s) a := same.symm ▸ admitted
    exact exactness.1 s a transferred

/-- Sufficiency is at the level of logic: the existential witness below is a
    `Prop`-valued relation, NOT an algorithm for a possibly infinite state space. -/
theorem separation_supports_exact_decisions
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (separation : Separates view admissible) :
    ∃ accept : Summary → Action → Prop,
      DecisionExact view admissible accept := by
  refine ⟨(fun q a => ∃ s, view s = q ∧ admissible s a), ?_⟩
  constructor
  · intro s a witness
    cases witness with
    | intro t facts =>
      exact (separation t s facts.1 a).mp facts.2
  · intro s a good
    exact ⟨s, rfl, good⟩

/-- Exact logical decisions through a view exist exactly when the view preserves
    the distinctions relevant to the specified admissibility predicate. -/
theorem exact_decisions_iff_separation
    (view : State → Summary)
    (admissible : State → Action → Prop) :
    (∃ accept : Summary → Action → Prop,
      DecisionExact view admissible accept) ↔
    Separates view admissible := by
  constructor
  · intro witness
    cases witness with
    | intro accept exactness =>
      exact exact_decisions_preserve_distinctions
        view admissible accept exactness
  · intro separation
    exact separation_supports_exact_decisions view admissible separation

/-- A computation on the same summary cannot undo an already lost distinction. -/
theorem postprocessing_cannot_repair_loss
    {Processed : Type z}
    (view : State → Summary)
    (process : Summary → Processed)
    (admissible : State → Action → Prop)
    (s t : State) (a : Action)
    (same : view s = view t)
    (good : admissible s a)
    (bad : ¬ admissible t a) :
    ¬ ∃ accept : Processed → Action → Prop,
        DecisionExact (fun x => process (view x)) admissible accept := by
  exact information_loss_impossibility
    (fun x => process (view x)) admissible s t a
    (congrArg process same) good bad

/-! ### Information loss across heterogeneous finite pipelines -/

/- A stage-indexed representation may change type from one stage to the next.
   The only structural assumption here is that each later representation is
   computed from the immediately preceding one. -/
theorem pipeline_preserves_indistinguishability
    {State : Type u} {Summary : Nat → Type v}
    (view : ∀ i, State → Summary i)
    (process : ∀ i, Summary i → Summary (Nat.succ i))
    (view_step : ∀ i s, view (Nat.succ i) s = process i (view i s))
    (k m : Nat) {s t : State}
    (same : view k s = view k t) :
    view (k + m) s = view (k + m) t := by
  induction m with
  | zero =>
    exact same
  | succ m ih =>
    change view (Nat.succ (k + m)) s = view (Nat.succ (k + m)) t
    rw [view_step, view_step]
    exact congrArg (process (k + m)) ih

/- A sound downstream decision must refuse the image of a state that collides
   with a state rejected for the same action. -/
theorem pipeline_loss_forces_refusal
    {State : Type u} {Summary : Nat → Type v} {Action : Type w}
    (view : ∀ i, State → Summary i)
    (process : ∀ i, Summary i → Summary (Nat.succ i))
    (view_step : ∀ i s, view (Nat.succ i) s = process i (view i s))
    (k m : Nat) (admissible : State → Action → Prop)
    (s t : State) (a : Action)
    (same : view k s = view k t)
    (bad : ¬ admissible t a) :
    ∀ accept : Summary (k + m) → Action → Prop,
      DecisionSound (view (k + m)) admissible accept →
      ¬ accept (view (k + m) s) a := by
  intro accept sound
  exact information_loss_forces_refusal
    (view (k + m)) admissible accept s t a
    (pipeline_preserves_indistinguishability view process view_step k m same)
    bad sound

/- A different logical decision may be chosen at every downstream length; the
   impossibility quantifies over all such choices. -/
theorem pipeline_information_loss_impossibility
    {State : Type u} {Summary : Nat → Type v} {Action : Type w}
    (view : ∀ i, State → Summary i)
    (process : ∀ i, Summary i → Summary (Nat.succ i))
    (view_step : ∀ i s, view (Nat.succ i) s = process i (view i s))
    (k m : Nat) (admissible : State → Action → Prop)
    (s t : State) (a : Action)
    (same : view k s = view k t)
    (good : admissible s a)
    (bad : ¬ admissible t a) :
    ¬ ∃ accept : Summary (k + m) → Action → Prop,
        DecisionExact (view (k + m)) admissible accept := by
  apply information_loss_impossibility
    (view (k + m)) admissible s t a
    (pipeline_preserves_indistinguishability view process view_step k m same)
    good bad

/- Exactness after further processing implies that the earlier representation
   already preserved every distinction relevant to the predicate. -/
theorem downstream_exactness_requires_upstream_separation
    {State : Type u} {Summary : Nat → Type v} {Action : Type w}
    (view : ∀ i, State → Summary i)
    (process : ∀ i, Summary i → Summary (Nat.succ i))
    (view_step : ∀ i s, view (Nat.succ i) s = process i (view i s))
    (k m : Nat) (admissible : State → Action → Prop)
    (exactness : ∃ accept : Summary (k + m) → Action → Prop,
        DecisionExact (view (k + m)) admissible accept) :
    Separates (view k) admissible := by
  cases exactness with
  | intro accept decisionExact =>
    have finalSeparation : Separates (view (k + m)) admissible :=
      exact_decisions_preserve_distinctions
        (view (k + m)) admissible accept decisionExact
    intro s t same a
    have sameAtEnd : view (k + m) s = view (k + m) t :=
      pipeline_preserves_indistinguishability view process view_step k m same
    exact finalSeparation s t sameAtEnd a

/-- If a coarser representation suffices, the representation it was computed
    from also suffices. This does not assume either representation is injective. -/
theorem separation_before_postprocessing
    {Processed : Type z}
    (view : State → Summary)
    (process : Summary → Processed)
    (admissible : State → Action → Prop)
    (h : Separates (fun x => process (view x)) admissible) :
    Separates view admissible := by
  intro s t same a
  exact h s t (congrArg process same) a

/-- Enriching a representation without losing the original representation
    preserves its logical sufficiency. No enrichment method is specified. -/
theorem recoverable_view_preserves_separation
    {Richer : Type z}
    (view : State → Summary)
    (richer : State → Richer)
    (recover : Richer → Summary)
    (recovers : ∀ s, recover (richer s) = view s)
    (admissible : State → Action → Prop)
    (h : Separates view admissible) :
    Separates richer admissible := by
  intro s t same a
  have coarseSame : view s = view t :=
    (recovers s).symm.trans ((congrArg recover same).trans (recovers t))
  exact h s t coarseSame a

/-- The identically refusing predicate is sound. This explicit witness prevents
    conflating the information-loss result with an impossibility of all safety. -/
theorem refusal_is_sound
    (view : State → Summary)
    (admissible : State → Action → Prop) :
    DecisionSound view admissible (fun _ _ => False) := by
  intro s a impossible
  exact False.elim impossible

/-- If any admissible pair exists, universal refusal is not complete. -/
theorem refusal_is_not_complete_when_progress_is_possible
    (view : State → Summary)
    (admissible : State → Action → Prop)
    (s : State) (a : Action) (good : admissible s a) :
    ¬ DecisionComplete view admissible (fun _ _ => False) := by
  intro complete
  exact complete s a good

end Information

/-! ## 2. Summary transfer conditions -/

/- A summary is transferable when some logical predicate on summaries accepts
   every guaranteed state in the chosen domain and accepts only states meeting
   the next requirement. The witness is a proposition, not an executable
   classifier. -/
def SummaryTransferable
    {State : Type u} {Summary : Type v}
    (view : State → Summary)
    (Domain Guaranteed Required : State → Prop) : Prop :=
  ∃ accept : Summary → Prop,
    (∀ s, Domain s → Guaranteed s → accept (view s)) ∧
    (∀ s, Domain s → accept (view s) → Required s)

/- Compatibility says that every summary collision inside the stated domain
   transports the guarantee to the required condition. -/
def SummaryCompatible
    {State : Type u} {Summary : Type v}
    (view : State → Summary)
    (Domain Guaranteed Required : State → Prop) : Prop :=
  ∀ s t,
    Domain s → Guaranteed s → Domain t →
    view s = view t → Required t

theorem summary_transferable_iff_compatible
    {State : Type u} {Summary : Type v}
    (view : State → Summary)
    (Domain Guaranteed Required : State → Prop) :
    SummaryTransferable view Domain Guaranteed Required ↔
      SummaryCompatible view Domain Guaranteed Required := by
  constructor
  · intro transferable
    cases transferable with
    | intro accept obligations =>
      intro s t domainS guaranteedS domainT same
      exact obligations.2 t domainT (same ▸ obligations.1 s domainS guaranteedS)
  · intro compatible
    refine ⟨(fun q => ∃ s, Domain s ∧ Guaranteed s ∧ view s = q), ?_⟩
    constructor
    · intro s domainS guaranteedS
      exact ⟨s, domainS, guaranteedS, rfl⟩
    · intro t domainT accepted
      cases accepted with
      | intro s witness =>
        exact compatible s t witness.1 witness.2.1 domainT witness.2.2

theorem summary_collision_prevents_transfer
    {State : Type u} {Summary : Type v}
    (view : State → Summary)
    (Domain Guaranteed Required : State → Prop)
    (s t : State)
    (domainS : Domain s) (guaranteedS : Guaranteed s)
    (domainT : Domain t) (same : view s = view t)
    (bad : ¬ Required t) :
    ¬ SummaryTransferable view Domain Guaranteed Required := by
  intro transferable
  have compatible :=
    (summary_transferable_iff_compatible view Domain Guaranteed Required).mp
      transferable
  exact bad (compatible s t domainS guaranteedS domainT same)

theorem summary_transfer_implies_compatibility
    {State : Type u} {Summary : Type v}
    (view : State → Summary)
    (Domain Guaranteed Required : State → Prop)
    (transferable : SummaryTransferable view Domain Guaranteed Required)
    (s : State) (domainS : Domain s) (guaranteedS : Guaranteed s) :
    Required s := by
  cases transferable with
  | intro accept obligations =>
    exact obligations.2 s domainS (obligations.1 s domainS guaranteedS)

/- The unit-action specialization explicitly connects summary transfer to the
   existing exact-decision/separation theorem. -/
theorem summary_transferable_iff_unit_exact_decision
    {State : Type u} {Summary : Type v}
    (view : State → Summary) (P : State → Prop) :
    SummaryTransferable view (fun _ => True) P P ↔
      ∃ accept : Summary → Unit → Prop,
        DecisionExact view (fun s (_ : Unit) => P s) accept := by
  constructor
  · intro transferable
    cases transferable with
    | intro accept obligations =>
      refine ⟨(fun q _ => accept q), ?_⟩
      constructor
      · intro s a accepted
        exact obligations.2 s True.intro accepted
      · intro s a good
        exact obligations.1 s True.intro good
  · intro exactWitness
    cases exactWitness with
    | intro accept exactness =>
      refine ⟨(fun q => accept q ()), ?_⟩
      constructor
      · intro s _ good
        exact exactness.2 s () good
      · intro s _ accepted
        exact exactness.1 s () accepted

theorem summary_transferable_iff_unit_separation
    {State : Type u} {Summary : Type v}
    (view : State → Summary) (P : State → Prop) :
    SummaryTransferable view (fun _ => True) P P ↔
      Separates view (fun s (_ : Unit) => P s) := by
  exact (summary_transferable_iff_unit_exact_decision view P).trans
    (exact_decisions_iff_separation view (fun s (_ : Unit) => P s))

/- A collision that persists through a heterogeneous pipeline also blocks any
   summary transfer at the downstream stage. -/
theorem pipeline_collision_prevents_transfer
    {State : Type u} {Summary : Nat → Type v}
    (view : ∀ i, State → Summary i)
    (process : ∀ i, Summary i → Summary (Nat.succ i))
    (view_step : ∀ i s, view (Nat.succ i) s = process i (view i s))
    (k m : Nat) (Domain Guaranteed Required : State → Prop)
    (s t : State)
    (domainS : Domain s) (guaranteedS : Guaranteed s)
    (domainT : Domain t) (same : view k s = view k t)
    (bad : ¬ Required t) :
    ¬ SummaryTransferable (view (k + m)) Domain Guaranteed Required := by
  apply summary_collision_prevents_transfer
    (view (k + m)) Domain Guaranteed Required s t domainS guaranteedS domainT
  · exact pipeline_preserves_indistinguishability view process view_step k m same
  · exact bad

/-! ## 3. Abstract contracts and relational composition -/

/-- Pure mathematical relations. No operational representation is prescribed. -/
abbrev Rel (X : Type u) (Y : Type v) := X → Y → Prop

/-- Predicate implication at an interface. -/
def Implies {X : Type u} (P Q : X → Prop) : Prop :=
  ∀ x, P x → Q x

/-- Ordinary relational composition. -/
def Compose {X : Type u} {Y : Type v} {Z : Type w}
    (R : Rel X Y) (T : Rel Y Z) : Rel X Z :=
  fun x z => ∃ y, R x y ∧ T y z

/-- Partial correctness of a relation under an explicit precondition. -/
def Triple {X : Type u} {Y : Type v}
    (P : X → Prop) (R : Rel X Y) (Q : Y → Prop) : Prop :=
  ∀ x y, P x → R x y → Q y

/-- Existence of a next transition is separate from partial correctness. -/
def TotalOn {X : Type u} {Y : Type v}
    (P : X → Prop) (R : Rel X Y) : Prop :=
  ∀ x, P x → ∃ y, R x y

/-- The replacement introduces no transitions outside the specification. -/
def Refines {X : Type u} {Y : Type v}
    (replacement specification : Rel X Y) : Prop :=
  ∀ x y, replacement x y → specification x y

/-- Consequence rule: strengthen the premise or weaken the conclusion. -/
theorem triple_consequence
    {X : Type u} {Y : Type v}
    (P P' : X → Prop) (Q Q' : Y → Prop) (R : Rel X Y)
    (pre : Implies P' P) (post : Implies Q Q')
    (correct : Triple P R Q) :
    Triple P' R Q' := by
  intro x y initial step
  exact post y (correct x y (pre x initial) step)

/-- Local contracts compose when the first conclusion establishes the next
    premise. Equality of these predicates is not required. -/
theorem compatible_contracts_compose
    {X : Type u} {Y : Type v} {Z : Type w}
    (P : X → Prop) (Q P' : Y → Prop) (Q' : Z → Prop)
    (R : Rel X Y) (T : Rel Y Z)
    (hLeft : Triple P R Q) (hRight : Triple P' T Q')
    (compatible : Implies Q P') :
    Triple P (Compose R T) Q' := by
  intro x z initial execution
  cases execution with
  | intro y steps =>
    exact hRight y z (compatible y (hLeft x y initial steps.1)) steps.2

/-- Sequential progress additionally needs transition existence for both parts. -/
theorem compatible_total_contracts_compose
    {X : Type u} {Y : Type v} {Z : Type w}
    (P : X → Prop) (Q P' : Y → Prop)
    (R : Rel X Y) (T : Rel Y Z)
    (leftCorrect : Triple P R Q)
    (leftTotal : TotalOn P R) (rightTotal : TotalOn P' T)
    (compatible : Implies Q P') :
    TotalOn P (Compose R T) := by
  intro x initial
  cases leftTotal x initial with
  | intro y leftStep =>
    have nextPre : P' y := compatible y (leftCorrect x y initial leftStep)
    cases rightTotal y nextPre with
    | intro z rightStep =>
      exact ⟨z, y, leftStep, rightStep⟩

/-- Grouping of relational composition does not change its meaning. -/
theorem composition_associative
    {W : Type u} {X : Type v} {Y : Type w} {Z : Type z}
    (R : Rel W X) (T : Rel X Y) (U : Rel Y Z)
    (s : W) (t : Z) :
    Compose (Compose R T) U s t ↔ Compose R (Compose T U) s t := by
  constructor
  · intro execution
    cases execution with
    | intro y facts =>
      cases facts.1 with
      | intro x earlier =>
        exact ⟨x, earlier.1, y, earlier.2, facts.2⟩
  · intro execution
    cases execution with
    | intro x facts =>
      cases facts.2 with
      | intro y later =>
        exact ⟨y, ⟨x, facts.1, later.1⟩, later.2⟩

/-- Behavioral refinement preserves partial correctness, but does not by itself
    promise that any transition still exists. -/
theorem triple_under_refinement
    {X : Type u} {Y : Type v}
    (P : X → Prop) (Q : Y → Prop)
    (replacement specification : Rel X Y)
    (refinement : Refines replacement specification)
    (correct : Triple P specification Q) :
    Triple P replacement Q := by
  intro x y initial transition
  exact correct x y initial (refinement x y transition)

/-- Refinement is itself compositional. -/
theorem refinement_composes
    {X : Type u} {Y : Type v} {Z : Type w}
    (R R' : Rel X Y) (T T' : Rel Y Z)
    (hLeft : Refines R' R) (hRight : Refines T' T) :
    Refines (Compose R' T') (Compose R T) := by
  intro x z execution
  cases execution with
  | intro y steps =>
    exact ⟨y, hLeft x y steps.1, hRight y z steps.2⟩

/-! ## 4. Every finite length, explicit hypotheses -/

/-- A finite sequence of stage-indexed abstract transitions, starting at stage 0.
    The relation at a stage may differ from the relation at every other stage. -/
inductive Runs {State : Type u} (step : Nat → Rel State State) :
    Nat → State → State → Prop where
  | zero (s : State) : Runs step 0 s s
  | succ {n : Nat} {s t q : State} :
      Runs step n s t → step n t q → Runs step (Nat.succ n) s q

/-- Generic induction principle for stage-specific boundary conditions. -/
theorem boundary_condition_induction
    {State : Type u}
    (step : Nat → Rel State State)
    (P : Nat → State → Prop)
    (advance : ∀ n, Triple (P n) (step n) (P (Nat.succ n))) :
    ∀ {n : Nat} {s t : State},
      Runs step n s t → P 0 s → P n t := by
  intro n s t execution
  induction execution with
  | zero s =>
    intro initial
    exact initial
  | succ hRun transition ih =>
    intro initial
    exact advance _ _ _ (ih initial) transition

/-- Abstract local guarantees and their interface compatibility. -/
def ConnectedContracts {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) : Prop :=
  (∀ n, Triple (Pre n) (step n) (Post n)) ∧
  (∀ n, Implies (Post n) (Pre (Nat.succ n)))

/- Contracts restricted to the finite window that is actually being used. -/
def ConnectedContractsUpTo {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) (N : Nat) : Prop :=
  (∀ i, i < N → Triple (Pre i) (step i) (Post i)) ∧
  (∀ i, i < N → Implies (Post i) (Pre (Nat.succ i)))

def PreservesOn {State : Type u}
    (Pre : State → Prop) (I : State → Prop)
    (step : Rel State State) : Prop :=
  ∀ s t, Pre s → I s → step s t → I t

theorem bounded_composition
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) (N k : Nat)
    (bound : k ≤ N)
    (contracts : ConnectedContractsUpTo step Pre Post N)
    {s t : State}
    (execution : Runs step k s t) (initial : Pre 0 s) :
    Pre k t := by
  induction execution with
  | zero s =>
    exact initial
  | @succ n s t q hRun transition ih =>
    have previousBound : n ≤ N := Nat.le_of_succ_le bound
    have stageBound : n < N :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) bound
    have previous : Pre n t := ih previousBound initial
    have post : Post n _ :=
      contracts.1 n stageBound _ _ previous transition
    exact contracts.2 n stageBound _ post

theorem bounded_prefix_invariant
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) (I : State → Prop) (N k : Nat)
    (bound : k ≤ N)
    (contracts : ConnectedContractsUpTo step Pre Post N)
    (preserves : ∀ i, i < N → PreservesOn (Pre i) I (step i))
    {s t : State}
    (execution : Runs step k s t)
    (initial : Pre 0 s) (invariant : I s) :
    Pre k t ∧ I t := by
  induction execution with
  | zero s =>
    exact ⟨initial, invariant⟩
  | @succ n s t q hRun transition ih =>
    have previousBound : n ≤ N := Nat.le_of_succ_le bound
    have stageBound : n < N :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) bound
    have previous : Pre n t ∧ I t :=
      ih previousBound initial invariant
    have post : Post n _ :=
      contracts.1 n stageBound _ _ previous.1 transition
    have nextPre : Pre (Nat.succ n) _ :=
      contracts.2 n stageBound _ post
    have nextInvariant : I _ :=
      preserves n stageBound _ _ previous.1 previous.2 transition
    exact ⟨nextPre, nextInvariant⟩

theorem bounded_progress
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) (N k : Nat)
    (bound : k ≤ N)
    (contracts : ConnectedContractsUpTo step Pre Post N)
    (total : ∀ i, i < N → TotalOn (Pre i) (step i))
    (s : State) (initial : Pre 0 s) :
    ∃ t, Runs step k s t ∧ Pre k t := by
  induction k generalizing s with
  | zero =>
    exact ⟨s, Runs.zero s, initial⟩
  | succ k ih =>
    have previousBound : k ≤ N := Nat.le_of_succ_le bound
    have stageBound : k < N :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self k) bound
    cases ih previousBound s initial with
    | intro q previous =>
      cases total k stageBound q previous.2 with
      | intro t transition =>
        have post : Post k t :=
          contracts.1 k stageBound q t previous.2 transition
        have nextPre : Pre (Nat.succ k) t :=
          contracts.2 k stageBound t post
        exact ⟨t, Runs.succ previous.1 transition, nextPre⟩

/- The information interface supplies the contract connection; a completed
   `ConnectedContracts` is not assumed as an input to this construction. -/
theorem summary_transfers_connect_contracts
    {State : Type u} {Summary : Nat → Type v}
    (step : Nat → Rel State State)
    (Pre Post Domain : Nat → State → Prop)
    (view : ∀ i, State → Summary i)
    (localCorrect : ∀ i, Triple (Pre i) (step i) (Post i))
    (postInDomain : ∀ i s, Post i s → Domain i s)
    (transfer : ∀ i,
      SummaryTransferable (view i) (Domain i) (Post i) (Pre (Nat.succ i))) :
    ConnectedContracts step Pre Post := by
  constructor
  · exact localCorrect
  · intro i s post
    exact summary_transfer_implies_compatibility
      (view i) (Domain i) (Post i) (Pre (Nat.succ i))
      (transfer i) s (postInDomain i s post) post

theorem summary_transfers_connect_contracts_up_to
    {State : Type u} {Summary : Nat → Type v}
    (step : Nat → Rel State State)
    (Pre Post Domain : Nat → State → Prop)
    (view : ∀ i, State → Summary i) (N : Nat)
    (localCorrect : ∀ i, i < N → Triple (Pre i) (step i) (Post i))
    (postInDomain : ∀ i, i < N → ∀ s, Post i s → Domain i s)
    (transfer : ∀ i, i < N →
      SummaryTransferable (view i) (Domain i) (Post i) (Pre (Nat.succ i))) :
    ConnectedContractsUpTo step Pre Post N := by
  constructor
  · exact localCorrect
  · intro i hi s post
    exact summary_transfer_implies_compatibility
      (view i) (Domain i) (Post i) (Pre (Nat.succ i))
      (transfer i hi) s (postInDomain i hi s post) post

/-- Every finite prefix establishes the next boundary precondition. The theorem
    quantifies over all executions of the stated relations, not just one demo. -/
theorem arbitrary_length_composition
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop)
    (contracts : ConnectedContracts step Pre Post) :
    ∀ {n : Nat} {s t : State},
      Runs step n s t → Pre 0 s → Pre n t := by
  have advance : ∀ n, Triple (Pre n) (step n) (Pre (Nat.succ n)) := by
    intro n s t initial transition
    exact contracts.2 n t (contracts.1 n s t initial transition)
  intro n s t execution initial
  exact boundary_condition_induction step Pre advance execution initial

/-- At the end of a nonempty sequence, the last local postcondition also holds. -/
theorem composed_last_postcondition
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop)
    (contracts : ConnectedContracts step Pre Post)
    {n : Nat} {s t : State}
    (execution : Runs step (Nat.succ n) s t)
    (initial : Pre 0 s) :
    Post n t := by
  cases execution with
  | succ hRun transition =>
    have boundary := arbitrary_length_composition step Pre Post
      contracts hRun initial
    exact contracts.1 _ _ _ boundary transition

/- If an invariant is preserved without a local premise at every stage, then
   the same invariant composes. This is why the counterexample below is about
   incompatible premises, not about all local invariant claims. -/
theorem unconditional_invariant_preservation_composes
    {State : Type u}
    (step : Nat → Rel State State) (I : State → Prop)
    (preserves : ∀ n, Triple I (step n) I) :
    ∀ {n : Nat} {s t : State}, Runs step n s t → I s → I t := by
  intro n s t execution
  induction execution with
  | zero s =>
    intro initial
    exact initial
  | succ hRun transition ih =>
    intro initial
    exact preserves _ _ _ (ih initial) transition

/- B -> C: summary transfer yields the interface obligations used by the
   bounded composition theorems below. -/
theorem summary_based_arbitrary_length_composition
    {State : Type u} {Summary : Nat → Type v}
    (step : Nat → Rel State State)
    (Pre Post Domain : Nat → State → Prop)
    (view : ∀ i, State → Summary i) (N k : Nat)
    (bound : k ≤ N)
    (localCorrect : ∀ i, i < N → Triple (Pre i) (step i) (Post i))
    (postInDomain : ∀ i, i < N → ∀ s, Post i s → Domain i s)
    (transfer : ∀ i, i < N →
      SummaryTransferable (view i) (Domain i) (Post i) (Pre (Nat.succ i)))
    {s t : State} (execution : Runs step k s t) (initial : Pre 0 s) :
    Pre k t := by
  exact bounded_composition step Pre Post N k bound
    (summary_transfers_connect_contracts_up_to step Pre Post Domain view N
      localCorrect postInDomain transfer)
    execution initial

theorem summary_based_composition_preserves_invariant
    {State : Type u} {Summary : Nat → Type v}
    (step : Nat → Rel State State)
    (Pre Post Domain : Nat → State → Prop)
    (view : ∀ i, State → Summary i) (I : State → Prop) (N k : Nat)
    (bound : k ≤ N)
    (localCorrect : ∀ i, i < N → Triple (Pre i) (step i) (Post i))
    (postInDomain : ∀ i, i < N → ∀ s, Post i s → Domain i s)
    (transfer : ∀ i, i < N →
      SummaryTransferable (view i) (Domain i) (Post i) (Pre (Nat.succ i)))
    (preserves : ∀ i, i < N → PreservesOn (Pre i) I (step i))
    {s t : State} (execution : Runs step k s t)
    (initial : Pre 0 s) (invariant : I s) :
    Pre k t ∧ I t := by
  exact bounded_prefix_invariant step Pre Post I N k bound
    (summary_transfers_connect_contracts_up_to step Pre Post Domain view N
      localCorrect postInDomain transfer)
    preserves execution initial invariant

/-- All modeled finite prefixes preserve the invariant, when both the contracts
    and the local invariant obligations have been established. -/
theorem all_prefixes_preserve_invariant
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop)
    (I : State → Prop)
    (contracts : ConnectedContracts step Pre Post)
    (preserves : ∀ n, PreservesOn (Pre n) I (step n)) :
    ∀ {n : Nat} {s t : State},
      Runs step n s t → Pre 0 s → I s → Pre n t ∧ I t := by
  have advance : ∀ n,
      Triple (fun s => Pre n s ∧ I s) (step n)
        (fun t => Pre (Nat.succ n) t ∧ I t) := by
    intro n s t initial transition
    constructor
    · exact contracts.2 n t (contracts.1 n s t initial.1 transition)
    · exact preserves n s t initial.1 initial.2 transition
  intro n s t execution initial invariant
  exact boundary_condition_induction step (fun n s => Pre n s ∧ I s)
    advance execution ⟨initial, invariant⟩

/-- With explicit local existence hypotheses, executions of each finite length
    exist. This is deliberately separate from the preceding universal claims. -/
theorem finite_progress
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop)
    (contracts : ConnectedContracts step Pre Post)
    (total : ∀ n, TotalOn (Pre n) (step n)) :
    ∀ n s, Pre 0 s → ∃ t, Runs step n s t ∧ Pre n t := by
  intro n
  induction n with
  | zero =>
    intro s initial
    exact ⟨s, Runs.zero s, initial⟩
  | succ n ih =>
    intro s initial
    cases ih s initial with
    | intro t hRun =>
      cases total n t hRun.2 with
      | intro q transition =>
        have nextCondition : Pre (Nat.succ n) q :=
          contracts.2 n q (contracts.1 n t q hRun.2 transition)
        exact ⟨q, Runs.succ hRun.1 transition, nextCondition⟩

/-- Joint non-vacuity and invariant result, still conditional on local progress. -/
theorem finite_progress_with_invariant
    {State : Type u}
    (step : Nat → Rel State State)
    (Pre Post : Nat → State → Prop)
    (I : State → Prop)
    (contracts : ConnectedContracts step Pre Post)
    (total : ∀ n, TotalOn (Pre n) (step n))
    (preserves : ∀ n, PreservesOn (Pre n) I (step n))
    (n : Nat) (s : State)
    (initial : Pre 0 s) (invariant : I s) :
    ∃ t, Runs step n s t ∧ Pre n t ∧ I t := by
  cases finite_progress step Pre Post contracts total n s initial with
  | intro t hRun =>
    have conditions := all_prefixes_preserve_invariant step Pre Post I
      contracts preserves hRun.1 initial invariant
    exact ⟨t, hRun.1, conditions.1, conditions.2⟩

/-! ## 5. Substitution and different internal state spaces -/

/-- Pointwise refinement of stage relations lifts to every finite execution. -/
theorem runs_under_refinement
    {State : Type u}
    (replacement specification : Nat → Rel State State)
    (refinement : ∀ n, Refines (replacement n) (specification n)) :
    ∀ {n : Nat} {s t : State},
      Runs replacement n s t → Runs specification n s t := by
  intro n s t execution
  induction execution with
  | zero s =>
    exact Runs.zero s
  | succ hRun transition ih =>
    exact Runs.succ ih (refinement _ _ _ transition)

/- The same lifting can be restricted to the stages of a finite window. -/
theorem bounded_runs_under_refinement
    {State : Type u}
    (replacement specification : Nat → Rel State State) (N n : Nat)
    (bound : n ≤ N)
    (refinement : ∀ i, i < N → Refines (replacement i) (specification i))
    {s t : State} :
    Runs replacement n s t → Runs specification n s t := by
  intro execution
  induction execution with
  | zero s =>
    exact Runs.zero s
  | @succ n s t q hRun transition ih =>
    have previousBound : n ≤ N := Nat.le_of_succ_le bound
    have stageBound : n < N :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) bound
    exact Runs.succ
      (ih previousBound)
      (refinement n stageBound _ _ transition)

theorem bounded_substitution_preserves_composition
    {State : Type u}
    (replacement specification : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) (N k : Nat)
    (bound : k ≤ N)
    (contracts : ConnectedContractsUpTo specification Pre Post N)
    (refinement : ∀ i, i < N → Refines (replacement i) (specification i))
    {s t : State} (execution : Runs replacement k s t)
    (initial : Pre 0 s) :
    Pre k t := by
  exact bounded_composition specification Pre Post N k bound contracts
    (bounded_runs_under_refinement replacement specification N k bound
      refinement execution)
    initial

theorem bounded_substitution_preserves_invariant
    {State : Type u}
    (replacement specification : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) (I : State → Prop) (N k : Nat)
    (bound : k ≤ N)
    (contracts : ConnectedContractsUpTo specification Pre Post N)
    (preserves : ∀ i, i < N → PreservesOn (Pre i) I (specification i))
    (refinement : ∀ i, i < N → Refines (replacement i) (specification i))
    {s t : State} (execution : Runs replacement k s t)
    (initial : Pre 0 s) (invariant : I s) :
    Pre k t ∧ I t := by
  exact bounded_prefix_invariant specification Pre Post I N k bound contracts
    preserves
    (bounded_runs_under_refinement replacement specification N k bound
      refinement execution)
    initial invariant

theorem bounded_substitution_preserves_progress
    {State : Type u}
    (replacement specification : Nat → Rel State State)
    (Pre Post : Nat → State → Prop) (N k : Nat)
    (bound : k ≤ N)
    (contracts : ConnectedContractsUpTo specification Pre Post N)
    (refinement : ∀ i, i < N → Refines (replacement i) (specification i))
    (replacementTotal : ∀ i, i < N → TotalOn (Pre i) (replacement i))
    (s : State) (initial : Pre 0 s) :
    ∃ t, Runs replacement k s t ∧ Pre k t := by
  have replacementContracts :
      ConnectedContractsUpTo replacement Pre Post N := by
    constructor
    · intro i hi
      exact triple_under_refinement
        (Pre i) (Post i) (replacement i) (specification i)
        (refinement i hi) (contracts.1 i hi)
    · exact contracts.2
  exact bounded_progress replacement Pre Post N k bound
    replacementContracts replacementTotal s initial

/-- Replacing any or all stages by behavioral refinements preserves the
    composition result. Progress of a replacement must be checked separately. -/
theorem substitution_preserves_composition
    {State : Type u}
    (replacement specification : Nat → Rel State State)
    (Pre Post : Nat → State → Prop)
    (contracts : ConnectedContracts specification Pre Post)
    (refinement : ∀ n, Refines (replacement n) (specification n)) :
    ∀ {n : Nat} {s t : State},
      Runs replacement n s t → Pre 0 s → Pre n t := by
  intro n s t execution initial
  exact arbitrary_length_composition specification Pre Post contracts
    (runs_under_refinement replacement specification refinement execution) initial

/-- Abstract forward simulation; no internal layout or implementation is given. -/
def ForwardSimulation
    {Concrete : Type u} {Abstract : Type v}
    (mapState : Concrete → Abstract)
    (concrete : Nat → Rel Concrete Concrete)
    (abstractStep : Nat → Rel Abstract Abstract) : Prop :=
  ∀ n s t, concrete n s t → abstractStep n (mapState s) (mapState t)

/-- Simulation lifts from individual transitions to every finite length. -/
theorem runs_under_simulation
    {Concrete : Type u} {Abstract : Type v}
    (mapState : Concrete → Abstract)
    (concrete : Nat → Rel Concrete Concrete)
    (abstractStep : Nat → Rel Abstract Abstract)
    (simulation : ForwardSimulation mapState concrete abstractStep) :
    ∀ {n : Nat} {s t : Concrete},
      Runs concrete n s t → Runs abstractStep n (mapState s) (mapState t) := by
  intro n s t execution
  induction execution with
  | zero s =>
    exact Runs.zero (mapState s)
  | succ hRun transition ih =>
    exact Runs.succ ih (simulation _ _ _ transition)

/-- A different internal state representation can inherit abstract boundary
    guarantees once the forward simulation is proved. -/
theorem simulation_preserves_invariant
    {Concrete : Type u} {Abstract : Type v}
    (mapState : Concrete → Abstract)
    (concrete : Nat → Rel Concrete Concrete)
    (abstractStep : Nat → Rel Abstract Abstract)
    (Pre Post : Nat → Abstract → Prop)
    (I : Abstract → Prop)
    (contracts : ConnectedContracts abstractStep Pre Post)
    (preserves : ∀ n, PreservesOn (Pre n) I (abstractStep n))
    (simulation : ForwardSimulation mapState concrete abstractStep) :
    ∀ {n : Nat} {s t : Concrete},
      Runs concrete n s t → Pre 0 (mapState s) → I (mapState s) →
        Pre n (mapState t) ∧ I (mapState t) := by
  intro n s t execution initial invariant
  exact all_prefixes_preserve_invariant abstractStep Pre Post I contracts preserves
    (runs_under_simulation mapState concrete abstractStep simulation execution)
    initial invariant

/-! ## 6. Fully specified, anonymous mathematical examples -/

namespace Examples

/-- Two opposite cases become indistinguishable under a constant summary. -/
def erasedView (_ : Bool) : Unit := ()

def boolAdmissible (s : Bool) (_ : Unit) : Prop := s = true

/-- A closed counterexample: its impossibility has no application hypotheses. -/
theorem erased_view_has_no_exact_decision :
    ¬ ∃ accept : Unit → Unit → Prop,
        DecisionExact erasedView boolAdmissible accept := by
  apply information_loss_impossibility
    erasedView boolAdmissible true false () rfl rfl
  intro impossible
  cases impossible

/-- The first coordinate matters for this example's predicate; the second does
    not. Thus sufficient information need not expose the complete state. -/
def projectedView (s : Bool × Bool) : Bool := s.1

def projectedAdmissible (s : Bool × Bool) (a : Bool) : Prop := s.1 = a

theorem projection_separates :
    Separates projectedView projectedAdmissible := by
  intro s t same a
  change s.1 = t.1 at same
  change (s.1 = a ↔ t.1 = a)
  constructor
  · intro good
    exact same.symm.trans good
  · intro good
    exact same.trans good

theorem projection_loses_state_information :
    ∃ s t : Bool × Bool, s ≠ t ∧ projectedView s = projectedView t := by
  refine ⟨(false, false), (false, true), ?_, rfl⟩
  intro same
  have impossible : (false : Bool) = true := congrArg Prod.snd same
  cases impossible

/-- Sufficiency for a fixed predicate does not require reconstruction of the
    whole state. This is a logical example, not a data-disclosure mechanism. -/
theorem partial_view_supports_exact_decisions :
    ∃ accept : Bool → Bool → Prop,
      DecisionExact projectedView projectedAdmissible accept := by
  exact separation_supports_exact_decisions
    projectedView projectedAdmissible projection_separates

/-- Anonymous symbols: they have no assigned device or workflow meaning. -/
inductive Point where
  | p
  | q
  | r

def invariant (s : Point) : Prop := s ≠ Point.r

def leftFn (_ : Point) : Point := Point.q

def rightFn : Point → Point
  | Point.p => Point.p
  | Point.q => Point.r
  | Point.r => Point.r

def leftRel (s t : Point) : Prop := t = leftFn s

def rightRel (s t : Point) : Prop := t = rightFn s

def leftPre (s : Point) : Prop := s = Point.p

def leftPost (s : Point) : Prop := s = Point.q

def rightPre (s : Point) : Prop := s = Point.p

def rightPost (s : Point) : Prop := s = Point.p

theorem invariant_p : invariant Point.p := by
  intro impossible
  cases impossible

theorem invariant_q : invariant Point.q := by
  intro impossible
  cases impossible

theorem not_invariant_r : ¬ invariant Point.r := by
  intro impossible
  exact impossible rfl

theorem left_correct : Triple leftPre leftRel leftPost := by
  intro s t _ transition
  exact transition

theorem right_correct : Triple rightPre rightRel rightPost := by
  intro s t initial transition
  change s = Point.p at initial
  cases initial
  exact transition

theorem left_total : TotalOn leftPre leftRel := by
  intro s _
  exact ⟨leftFn s, rfl⟩

theorem right_total : TotalOn rightPre rightRel := by
  intro s _
  exact ⟨rightFn s, rfl⟩

theorem left_preserves : PreservesOn leftPre invariant leftRel := by
  intro s t _ _ transition
  change t = Point.q at transition
  cases transition
  exact invariant_q

theorem right_preserves : PreservesOn rightPre invariant rightRel := by
  intro s t initial _ transition
  have final := right_correct s t initial transition
  change t = Point.p at final
  cases final
  exact invariant_p

theorem contracts_are_incompatible : ¬ Implies leftPost rightPre := by
  intro compatible
  have impossible : Point.q = Point.p := compatible Point.q rfl
  cases impossible

theorem unsafe_composite_execution :
    Compose leftRel rightRel Point.p Point.r := by
  exact ⟨Point.q, rfl, rfl⟩

/-- Non-vacuous local correctness, local progress, and preservation of the SAME
    invariant under each local premise still do not establish safe composition
    when the premises are incompatible. Both premises have an inhabitant. -/
theorem local_assurance_does_not_automatically_compose :
    Triple leftPre leftRel leftPost ∧
    Triple rightPre rightRel rightPost ∧
    TotalOn leftPre leftRel ∧
    TotalOn rightPre rightRel ∧
    PreservesOn leftPre invariant leftRel ∧
    PreservesOn rightPre invariant rightRel ∧
    (∃ s, leftPre s ∧ invariant s) ∧
    (∃ s, rightPre s ∧ invariant s) ∧
    ¬ Triple leftPre (Compose leftRel rightRel) invariant := by
  refine ⟨left_correct, right_correct, left_total, right_total,
    left_preserves, right_preserves,
    ⟨Point.p, rfl, invariant_p⟩, ⟨Point.p, rfl, invariant_p⟩, ?_⟩
  intro compositeCorrect
  exact not_invariant_r
    (compositeCorrect Point.p Point.r rfl unsafe_composite_execution)

/-- The same finite state space also gives a nontrivial positive model. -/
def swapFn : Point → Point
  | Point.p => Point.q
  | Point.q => Point.p
  | Point.r => Point.r

def swapRel (s t : Point) : Prop := t = swapFn s

theorem swap_correct : Triple invariant swapRel invariant := by
  intro s t initial transition
  change t = swapFn s at transition
  cases transition
  cases s with
  | p => exact invariant_q
  | q => exact invariant_p
  | r => exact False.elim (initial rfl)

def swapStages (_ : Nat) : Rel Point Point := swapRel

def swapBoundary (_ : Nat) : Point → Prop := invariant

theorem swap_contracts :
    ConnectedContracts swapStages swapBoundary swapBoundary := by
  constructor
  · intro n
    exact swap_correct
  · intro n s initial
    exact initial

theorem swap_total : ∀ n, TotalOn (swapBoundary n) (swapStages n) := by
  intro n s _
  exact ⟨swapFn s, rfl⟩

theorem swap_preserves :
    ∀ n, PreservesOn (swapBoundary n) invariant (swapStages n) := by
  intro n s t initial _ transition
  exact swap_correct s t initial transition

/-- Non-vacuity at every finite length, including positive lengths; the invariant
    excludes `Point.r`, so this is not an invariant defined as universally true. -/
theorem safe_runs_exist_at_every_finite_length (n : Nat) :
    ∃ t, Runs swapStages n Point.p t ∧ invariant t := by
  cases finite_progress_with_invariant
      swapStages swapBoundary swapBoundary invariant
      swap_contracts swap_total swap_preserves n Point.p invariant_p invariant_p with
  | intro t facts =>
    exact ⟨t, facts.1, facts.2.2⟩

/-- Universal correctness and existence are both witnessed by the positive model. -/
theorem every_swap_prefix_is_safe
    {n : Nat} {t : Point} (execution : Runs swapStages n Point.p t) :
    invariant t := by
  exact (all_prefixes_preserve_invariant
    swapStages swapBoundary swapBoundary invariant swap_contracts swap_preserves
    execution invariant_p invariant_p).2

/-- A behavior-removing refinement is still a refinement. This counterexample
    prevents deriving progress from refinement alone. -/
def noTransition (_ _ : Unit) : Prop := False

def identityTransition (s t : Unit) : Prop := t = s

theorem refinement_alone_does_not_guarantee_progress :
    Refines noTransition identityTransition ∧
    TotalOn (fun _ : Unit => True) identityTransition ∧
    ¬ TotalOn (fun _ : Unit => True) noTransition := by
  constructor
  · intro s t impossible
    exact False.elim impossible
  · constructor
    · intro s _
      exact ⟨s, rfl⟩
    · intro total
      cases total () True.intro with
      | intro t impossible =>
        exact impossible

/- A heterogeneous anonymous pipeline: the initial representation is `Bool`,
   while every later representation is `Unit`. The collision is introduced at
   the first transition rather than at stage zero. -/
def HSummary : Nat → Type
  | 0 => Bool
  | _ => Unit

def heterogeneousView : (i : Nat) → Bool → HSummary i
  | 0, s => s
  | Nat.succ _, _ => ()

def heterogeneousProcess :
    (i : Nat) → HSummary i → HSummary (Nat.succ i)
  | 0, _ => ()
  | Nat.succ _, _ => ()

theorem heterogeneous_view_step :
    ∀ i s, heterogeneousView (Nat.succ i) s =
      heterogeneousProcess i (heterogeneousView i s) := by
  intro i s
  cases i <;> rfl

def pipelineAdmissible (s : Bool) (_ : Unit) : Prop := s = true

theorem multistage_information_loss_persists (m : Nat) :
    heterogeneousView (Nat.succ 0 + m) true =
      heterogeneousView (Nat.succ 0 + m) false := by
  apply pipeline_preserves_indistinguishability
    heterogeneousView heterogeneousProcess heterogeneous_view_step
    (Nat.succ 0) m (s := true) (t := false)
  rfl

theorem multistage_information_loss_blocks_exactness (m : Nat) :
    ¬ ∃ accept : HSummary (Nat.succ 0 + m) → Unit → Prop,
        DecisionExact (heterogeneousView (Nat.succ 0 + m))
          pipelineAdmissible accept := by
  apply pipeline_information_loss_impossibility
    heterogeneousView heterogeneousProcess heterogeneous_view_step
    (Nat.succ 0) m pipelineAdmissible true false ()
  · rfl
  · rfl
  · intro impossible
    cases impossible

/- An independently available, state-distinguishing representation can support
   an exact logical predicate. No postprocessing factorization is assumed here,
   so this is outside the scope of the preceding pipeline impossibility. -/
def identityBoolView (s : Bool) : Bool := s

theorem identity_bool_separates :
    Separates identityBoolView boolAdmissible := by
  intro s t same a
  change s = t at same
  cases same
  constructor <;> intro h <;> exact h

theorem additional_information_can_restore_exactness :
    ∃ accept : Bool → Unit → Prop,
      DecisionExact identityBoolView boolAdmissible accept := by
  exact separation_supports_exact_decisions
    identityBoolView boolAdmissible identity_bool_separates

/- A closed transfer counterexample: both states are in the domain, one is
   guaranteed, and the colliding state fails the next requirement. -/
def transferDomain (_ : Bool) : Prop := True

def transferGuaranteed (s : Bool) : Prop := s = true

def transferRequired (s : Bool) : Prop := s = true

theorem erased_summary_cannot_transfer_guarantee :
    transferDomain true ∧ transferGuaranteed true ∧
    transferDomain false ∧ ¬ transferRequired false ∧
    ¬ SummaryTransferable erasedView transferDomain
      transferGuaranteed transferRequired := by
  refine ⟨True.intro, rfl, True.intro, ?_, ?_⟩
  · intro impossible
    cases impossible
  · exact summary_collision_prevents_transfer
      erasedView transferDomain transferGuaranteed transferRequired
      true false True.intro rfl True.intro rfl (by
        intro impossible
        cases impossible)

/- A projection forgets one coordinate yet transfers the selected property. -/
def projectedProperty (s : Bool × Bool) : Prop := s.1 = true

theorem projection_transfers_without_full_reconstruction :
    SummaryTransferable projectedView (fun _ => True)
      projectedProperty projectedProperty ∧
    (∃ s t : Bool × Bool, s ≠ t ∧ projectedView s = projectedView t) := by
  constructor
  · apply (summary_transferable_iff_compatible projectedView
      (fun _ => True) projectedProperty projectedProperty).mpr
    intro s t _ good _ same
    change s.1 = true at good
    change s.1 = t.1 at same
    change t.1 = true
    exact same.symm.trans good
  · exact projection_loses_state_information

/- The following summary interface is intentionally identity-like only within
   this anonymous positive model; the main theorem still receives its transfer
   proof as an explicit hypothesis. -/
def swapSummary (_ : Nat) : Type := Point

def swapView (_ : Nat) (s : Point) : Point := s

def swapDomain (_ : Nat) (s : Point) : Prop := invariant s

def swapGuaranteed (_ : Nat) (s : Point) : Prop := invariant s

def swapRequired (_ : Nat) (s : Point) : Prop := invariant s

theorem swap_summary_transfer :
    ∀ i, SummaryTransferable (swapView i) (swapDomain i)
      (swapGuaranteed i) (swapRequired (Nat.succ i)) := by
  intro i
  refine ⟨(fun summary => invariant summary), ?_⟩
  constructor
  · intro s _ good
    exact good
  · intro s _ accepted
    exact accepted

theorem twoSwapExecution : Runs swapStages 2 Point.p Point.p := by
  have first : swapStages 0 Point.p Point.q := by
    rfl
  have second : swapStages 1 Point.q Point.p := by
    rfl
  exact Runs.succ (Runs.succ (Runs.zero Point.p) first) second

theorem summary_based_two_stage_safe_execution :
    ∃ t, Runs swapStages 2 Point.p t ∧ invariant t := by
  have result := summary_based_composition_preserves_invariant
    swapStages swapBoundary swapBoundary swapDomain swapView invariant 2 2
    (by exact Nat.le_refl 2)
    (by intro i hi; exact swap_correct)
    (by intro i hi s post; exact post)
    (by
      intro i hi
      change SummaryTransferable (swapView i) (swapDomain i)
        (swapBoundary i) (swapBoundary (Nat.succ i))
      exact swap_summary_transfer i)
    (by intro i hi; exact swap_preserves i)
    twoSwapExecution invariant_p invariant_p
  exact ⟨Point.p, twoSwapExecution, result.2⟩

/- The finite-window example intentionally makes stage two unsafe, while the
   first two stages satisfy exactly the assumptions used by the bounded result. -/
def finiteWindowStages (i : Nat) : Rel Point Point :=
  if i < 2 then swapRel else rightRel

theorem finite_window_contracts_up_to_two :
    ConnectedContractsUpTo finiteWindowStages swapBoundary swapBoundary 2 := by
  constructor
  · intro i hi
    have stage : finiteWindowStages i = swapRel := by
      simp [finiteWindowStages, hi]
    rw [stage]
    exact swap_correct
  · intro i hi s post
    exact post

theorem finite_window_stage_two_is_not_locally_safe :
    ¬ Triple (swapBoundary 2) (finiteWindowStages 2) (swapBoundary 2) := by
  intro correct
  have badStep : finiteWindowStages 2 Point.q Point.r := by
    simp [finiteWindowStages, rightRel, rightFn]
  exact not_invariant_r (correct Point.q Point.r invariant_q badStep)

theorem finite_window_composition_needs_no_future_contracts :
    ∃ t, Runs finiteWindowStages 2 Point.p t ∧ invariant t := by
  have first : finiteWindowStages 0 Point.p Point.q := by
    simp [finiteWindowStages, swapRel, swapFn]
  have second : finiteWindowStages 1 Point.q Point.p := by
    simp [finiteWindowStages, swapRel, swapFn]
  have execution : Runs finiteWindowStages 2 Point.p Point.p :=
    Runs.succ (Runs.succ (Runs.zero Point.p) first) second
  have result := bounded_prefix_invariant
    finiteWindowStages swapBoundary swapBoundary invariant 2 2
    (by exact Nat.le_refl 2) finite_window_contracts_up_to_two
    (by
      intro i hi
      have stage : finiteWindowStages i = swapRel := by
        simp [finiteWindowStages, hi]
      rw [stage]
      exact swap_preserves i)
    execution invariant_p invariant_p
  exact ⟨Point.p, execution, result.2⟩

end Examples

/-! ## 7. Principal-result dependency audit

These commands inspect dependencies, not physical modeling assumptions. The
latter appear explicitly as quantified parameters and hypotheses above.
-/

#print axioms information_loss_impossibility
#print axioms exact_decisions_iff_separation
#print axioms postprocessing_cannot_repair_loss
#print axioms pipeline_preserves_indistinguishability
#print axioms pipeline_information_loss_impossibility
#print axioms downstream_exactness_requires_upstream_separation
#print axioms summary_transferable_iff_compatible
#print axioms summary_transferable_iff_unit_separation
#print axioms summary_collision_prevents_transfer
#print axioms summary_transfers_connect_contracts
#print axioms summary_transfers_connect_contracts_up_to
#print axioms arbitrary_length_composition
#print axioms bounded_composition
#print axioms bounded_prefix_invariant
#print axioms bounded_progress
#print axioms summary_based_arbitrary_length_composition
#print axioms summary_based_composition_preserves_invariant
#print axioms all_prefixes_preserve_invariant
#print axioms finite_progress_with_invariant
#print axioms substitution_preserves_composition
#print axioms bounded_substitution_preserves_composition
#print axioms bounded_substitution_preserves_invariant
#print axioms bounded_substitution_preserves_progress
#print axioms simulation_preserves_invariant
#print axioms unconditional_invariant_preservation_composes
#print axioms Examples.local_assurance_does_not_automatically_compose
#print axioms Examples.safe_runs_exist_at_every_finite_length
#print axioms Examples.refinement_alone_does_not_guarantee_progress
#print axioms Examples.multistage_information_loss_blocks_exactness
#print axioms Examples.additional_information_can_restore_exactness
#print axioms Examples.erased_summary_cannot_transfer_guarantee
#print axioms Examples.projection_transfers_without_full_reconstruction
#print axioms Examples.summary_based_two_stage_safe_execution
#print axioms Examples.finite_window_composition_needs_no_future_contracts
#print axioms Examples.finite_window_stage_two_is_not_locally_safe

end PhysicalAIPublicComposition
