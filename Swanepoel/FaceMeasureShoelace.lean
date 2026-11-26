module
public import Swanepoel.FaceSliceFlux
public import Swanepoel.PhysicalSectorArea
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sectorChart_cartesian (x y : ℝ) : sectorChart 0 0 (x,y)=cartPoint x y := by
  apply planeComplex_injective
  rw [sectorChart_complex]
  apply Complex.ext <;> simp [planeComplex,unitAngleVector,cartPoint]

theorem PennyGraph.face_measure_eq_slice_integral {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val) :
    volume.real F.val=∫ x : ℝ,∫ y : ℝ,G.faceSliceValue F x y := by
  let S : Set (ℝ×ℝ) := (sectorChart 0 0) ⁻¹' F.val
  have hS : MeasurableSet S := (sectorChart 0 0).measurable F.property.isOpen.measurableSet
  have hmeasure : volume S=volume F.val := (sectorChart_preserves_volume 0 0).measure_preimage_equiv F.val
  have hfinite : volume S≠⊤ := by rw [hmeasure]; exact hF.measure_lt_top.ne
  have hint : Integrable (S.indicator (fun _ : ℝ×ℝ => (1:ℝ))) :=
    (integrable_indicator_iff hS).mpr (integrableOn_const hfinite)
  have hfun : S.indicator (fun _ : ℝ×ℝ => (1:ℝ))=
      (fun z : ℝ×ℝ => G.faceSliceValue F z.1 z.2) := by
    funext z
    rcases z with ⟨x,y⟩
    simp only [S,Set.indicator,Set.mem_preimage,sectorChart_cartesian,PennyGraph.faceSliceValue]
  calc
    volume.real F.val=volume.real S := by simp only [measureReal_def,hmeasure]
    _ = ∫ z : ℝ×ℝ,S.indicator (fun _ => (1:ℝ)) z := (integral_indicator_one hS).symm
    _ = ∫ x : ℝ,∫ y : ℝ,S.indicator (fun _ => (1:ℝ)) (x,y) := integral_prod _ hint
    _ = ∫ x : ℝ,∫ y : ℝ,G.faceSliceValue F x y := by rw [hfun]

theorem PennyGraph.faceSignedArea_eq_measure {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val) :
    G.faceSignedArea G.point F=volume.real F.val := by
  obtain ⟨R₀,hR₀⟩ := isBounded_iff_forall_norm_le.mp hF
  obtain ⟨M,hM⟩ := (Set.finite_range (fun v : Fin n => ‖G.point v‖)).bddAbove
  let R := max R₀ M+1
  have hv (v : Fin n) : |G.point v 1|<R := by
    have hcoord := PiLp.norm_apply_le (G.point v) (1:Fin 2)
    rw [Real.norm_eq_abs] at hcoord
    have hh := hM ⟨v,rfl⟩
    dsimp [R]
    linarith only [hcoord,hh,le_max_right R₀ M]
  have hbound (z : Plane) (hz : z∈F.val) : |z 1|<R := by
    have hcoord := PiLp.norm_apply_le z (1:Fin 2)
    rw [Real.norm_eq_abs] at hcoord
    have hh := hR₀ z hz
    dsimp [R]
    linarith only [hcoord,hh,le_max_left R₀ M]
  have hregular : ∀ᵐ x : ℝ,∀ v : Fin n,x≠G.point v 0 :=
    Filter.eventually_all.mpr (fun v => volume.ae_ne (G.point v 0))
  symm
  calc
    volume.real F.val=∫ x : ℝ,∫ y : ℝ,G.faceSliceValue F x y :=
      G.face_measure_eq_slice_integral F hF
    _ = ∫ x : ℝ,∑ e : ContactEdge G,G.edgeSliceFlux F R e x := by
      apply integral_congr_ae
      filter_upwards [hregular] with x hx
      exact G.faceSlice_integral_eq_flux F hF R hv hbound x hx
    _ = ∑ e : ContactEdge G,∫ x : ℝ,G.edgeSliceFlux F R e x :=
      integral_finsetSum _ (fun e _ => G.edgeSliceFlux_integrable F R e)
    _ = ∑ e : ContactEdge G,G.faceIncidence F e*(G.point e.val.2 0-G.point e.val.1 0)*
        ((G.point e.val.1 1+G.point e.val.2 1)/2+R) :=
      Finset.sum_congr rfl (fun e _ => G.edgeSliceFlux_integral F R e)
    _ = G.faceSignedArea G.point F := G.boundary_flux_eq_faceSignedArea F R

end Swanepoel
