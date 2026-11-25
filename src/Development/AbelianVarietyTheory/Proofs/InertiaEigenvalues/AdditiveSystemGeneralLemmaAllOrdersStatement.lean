module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrders
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_all_orders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  first | exact @GlobalTheory.PMonE.generalLemma_allOrders | exact GlobalTheory.PMonE.generalLemma_allOrders | (intros; apply GlobalTheory.PMonE.generalLemma_allOrders <;> assumption)
