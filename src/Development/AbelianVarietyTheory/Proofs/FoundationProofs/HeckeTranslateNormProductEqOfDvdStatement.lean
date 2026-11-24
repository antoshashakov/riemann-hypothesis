module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvd
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  first | exact @GlobalTheory.KZ.ES.Nq_eq_of_dvd | exact GlobalTheory.KZ.ES.Nq_eq_of_dvd | (intros; apply GlobalTheory.KZ.ES.Nq_eq_of_dvd <;> assumption)
