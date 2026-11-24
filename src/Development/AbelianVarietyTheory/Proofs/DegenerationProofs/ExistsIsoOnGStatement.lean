module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_numD_iso_onG_of_allMatch : AllMatch fun {_} _ {N} {N'} {_} μ _ _ => μ.A → ∀ e, μ.B e → μ.Term e → ∀ I : NumB.Iso N.toNumB N'.toNumB, μ.OnB I → ∃ J : NumD.Iso N N', J.toIso = I ∧ J.e = e ∧ μ.OnG J := by
  first | exact @GlobalTheory.Ex.RecPeriods.exists_iso_onG | exact GlobalTheory.Ex.RecPeriods.exists_iso_onG | (intros; apply GlobalTheory.Ex.RecPeriods.exists_iso_onG <;> assumption)
