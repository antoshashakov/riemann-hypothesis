module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMapStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChartStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonemptyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalizationStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFractionStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinExists

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.exists_join_model_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i :=
  @_root_.PositivityTheory.HtPt.Mb.join_exists
