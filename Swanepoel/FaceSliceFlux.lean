module
public import Swanepoel.FaceSliceIntegral
public import Swanepoel.EdgeSliceIntegral
public import Swanepoel.FaceSignedArea
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ContactEdge.slice_jump_eq_incidence {n : ℕ} {G : PennyGraph n} (e : ContactEdge G)
    (F : PlaneFace G) :
    faceIndicatorValue F e.sliceLowerFace-faceIndicatorValue F e.sliceUpperFace=
      if 0<G.point e.val.2 0-G.point e.val.1 0 then G.faceIncidence F e else -G.faceIncidence F e := by
  unfold ContactEdge.sliceLowerFace ContactEdge.sliceUpperFace PennyGraph.faceIncidence faceIndicatorValue
  split_ifs <;> ring

def PennyGraph.edgeSliceFlux {n : ℕ} (G : PennyGraph n) (F : PlaneFace G)
    (R : ℝ) (e : ContactEdge G) : ℝ→ℝ :=
  (Ioo (min (G.point e.val.1 0) (G.point e.val.2 0))
    (max (G.point e.val.1 0) (G.point e.val.2 0))).indicator
      (fun x => (faceIndicatorValue F e.sliceLowerFace-faceIndicatorValue F e.sliceUpperFace)*(e.sliceHeight x+R))

theorem PennyGraph.edgeSliceFlux_integrable {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (R : ℝ) (e : ContactEdge G) : Integrable (G.edgeSliceFlux F R e) := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  have hc : Continuous (fun x : ℝ =>
      (faceIndicatorValue F e.sliceLowerFace-faceIndicatorValue F e.sliceUpperFace)*(e.sliceHeight x+R)) := by
    unfold ContactEdge.sliceHeight ContactEdge.sliceParameter
    fun_prop
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem PennyGraph.edgeSliceFlux_integral {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (R : ℝ) (e : ContactEdge G) :
    (∫ x,G.edgeSliceFlux F R e x)=G.faceIncidence F e*
      (G.point e.val.2 0-G.point e.val.1 0)*((G.point e.val.1 1+G.point e.val.2 1)/2+R) := by
  rw [PennyGraph.edgeSliceFlux,integral_indicator measurableSet_Ioo]
  simp_rw [e.slice_jump_eq_incidence F]
  exact oriented_edge_slice_integral _ _ _ _ _ _

theorem PennyGraph.faceSlice_integral_eq_flux {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val) (R : ℝ)
    (hv : ∀ v : Fin n,|G.point v 1|<R) (hbound : ∀ z∈F.val,|z 1|<R)
    (x : ℝ) (hx : ∀ v : Fin n,x≠G.point v 0) :
    (∫ y,G.faceSliceValue F x y)=∑ e : ContactEdge G,G.edgeSliceFlux F R e x := by
  rw [G.faceSlice_integral F hF R hv hbound x hx]
  unfold PennyGraph.sliceEdges
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [PennyGraph.edgeSliceFlux,Set.indicator,Set.mem_Ioo]

theorem PennyGraph.boundary_flux_eq_faceSignedArea {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (R : ℝ) :
    (∑ e : ContactEdge G,G.faceIncidence F e*(G.point e.val.2 0-G.point e.val.1 0)*
      ((G.point e.val.1 1+G.point e.val.2 1)/2+R))=G.faceSignedArea G.point F := by
  have hxy := G.face_incidence_gradient_sum F (fun v => G.point v 0*G.point v 1)
  have hx := G.face_incidence_gradient_sum F (fun v => G.point v 0)
  have hrev (e : OrientedEdge G) : cross2 (G.point (reverseEdge e).val.1) (G.point (reverseEdge e).val.2)=
      -cross2 (G.point e.val.1) (G.point e.val.2) := by
    simp only [reverseEdge,cross2]
    ring
  have hcross := G.face_dart_curl_eq_incidence_sum F
    (fun e => cross2 (G.point e.val.1) (G.point e.val.2)) hrev
  have htwo : 2*(∑ e : ContactEdge G,G.faceIncidence F e*(G.point e.val.2 0-G.point e.val.1 0)*
      ((G.point e.val.1 1+G.point e.val.2 1)/2+R))=
      -(∑ e : ContactEdge G,G.faceIncidence F e*cross2 (G.point e.val.1) (G.point e.val.2))+
      (∑ e : ContactEdge G,G.faceIncidence F e*(G.point e.val.2 0*G.point e.val.2 1-
        G.point e.val.1 0*G.point e.val.1 1))+
      (2*R)*(∑ e : ContactEdge G,G.faceIncidence F e*(G.point e.val.2 0-G.point e.val.1 0)) := by
    simp only [Finset.mul_sum,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    unfold cross2
    ring
  rw [hxy,hx] at htwo
  simp only [smul_eq_mul,ContactEdge.forwardEdge] at hcross
  unfold PennyGraph.faceSignedArea
  rw [hcross]
  linarith only [htwo]

end Swanepoel
