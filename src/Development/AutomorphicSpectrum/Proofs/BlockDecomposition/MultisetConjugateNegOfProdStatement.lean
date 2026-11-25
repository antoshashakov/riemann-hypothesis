module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProd
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.RealPlaceAnalysis.StatementA

@[expose] public section

open Formalism.REAL

theorem _root_.GlobalTheory.T.multiset_conjugate_neg_of_prod : ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n → (∀ u : ℂ, (m.map (u + ·)).prod = (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | exact GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | (intros; apply GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq <;> assumption)
