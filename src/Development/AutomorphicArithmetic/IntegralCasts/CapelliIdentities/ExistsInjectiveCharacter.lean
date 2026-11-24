module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Complex.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

theorem UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char :
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
    ∃ (lam0 : (ZMod p)ˣ →* ℂˣ), Function.Injective (⇑lam0 : (ZMod p)ˣ → ℂˣ) := by
  intro p inst
  haveI : NeZero (Nat.card (ZMod p)ˣ) := ⟨Nat.card_pos.ne'⟩
  have hcard : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ) :=
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ (Nat.card (ZMod p)ˣ)).symm
  let e : (ZMod p)ˣ ≃* rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ := mulEquivOfCyclicCardEq hcard
  exact ⟨(rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ).subtype.comp e.toMonoidHom,
    (Subgroup.subtype_injective _).comp e.injective⟩
