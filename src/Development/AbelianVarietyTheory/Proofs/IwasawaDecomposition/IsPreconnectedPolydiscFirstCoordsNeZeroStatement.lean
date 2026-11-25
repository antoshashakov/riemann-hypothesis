module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPreconnectedPolydiscFirstCoordsNeZero
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero : ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  first | exact @GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | exact GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | (intros; apply GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero <;> assumption)
