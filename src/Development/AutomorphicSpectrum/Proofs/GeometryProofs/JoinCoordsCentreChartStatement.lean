module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.join_coords_centre_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.join_points_charts | exact GlobalTheory.CompanionTheory.Ar.join_points_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.join_points_charts <;> assumption)
