module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiag
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.kronecker_congruence_frobenius_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a → SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  first | exact @GlobalTheory.KZ.ES.kron_frob_diag | exact GlobalTheory.KZ.ES.kron_frob_diag | (intros; apply GlobalTheory.KZ.ES.kron_frob_diag <;> assumption)
