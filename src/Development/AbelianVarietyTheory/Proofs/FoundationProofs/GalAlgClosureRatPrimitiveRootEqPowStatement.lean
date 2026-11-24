module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPow
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q → ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  first | exact @GlobalTheory.algEquiv_primitiveRoot_pow | exact GlobalTheory.algEquiv_primitiveRoot_pow | (intros; apply GlobalTheory.algEquiv_primitiveRoot_pow <;> assumption)
