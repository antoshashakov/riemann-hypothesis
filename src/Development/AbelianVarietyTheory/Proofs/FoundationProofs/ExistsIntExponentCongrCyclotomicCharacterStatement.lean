module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacter
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ), 0 < M → l ^ n ∣ M → ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧ (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  first | exact @GlobalTheory.KZ.exists_int_exponent_cyclotomic | exact GlobalTheory.KZ.exists_int_exponent_cyclotomic | (intros; apply GlobalTheory.KZ.exists_int_exponent_cyclotomic <;> assumption)
