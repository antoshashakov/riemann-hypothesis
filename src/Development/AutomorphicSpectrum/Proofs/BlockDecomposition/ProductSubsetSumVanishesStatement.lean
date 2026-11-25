module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSubsetSumVanishes
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.product_subset_sum_vanishes : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ) (m : Multiset ℂ) (A B : R[X]), 0 < r → A.Monic → B.Monic → A.natDegree = r →
  A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod →
  ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | exact GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | (intros; apply GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex <;> assumption)
