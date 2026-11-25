module

public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUnique
import Supplements.MathlibImports.AnalysisAndTactics
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace

@[expose] public section

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.cuspidal_label_unique : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) (P P' : K[X]),
    HasCuspLabel C τ P → HasCuspLabel C τ P' → P = P' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique | exact GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique | (intros; apply GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique <;> assumption)
