module
public import Swanepoel.HalfLocalBankData
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace HalfLocalBankData
variable {n : ℕ} {G : PennyGraph n} {cut v : TrackComponent G}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    {P : HalfCutPiece B ht side v} (V : HalfLocalBankData P)

theorem crossing_signed_normal_pos (hcut : cut∈G.ordinaryTrackComponents)
    (hUV : ComponentCrosses cut v) (e : OrientedEdge G) (he : SpineSource e)
    (heY : G.sourceFace e∈B.bankDefectFamily ht side)
    (hcross : ComponentCrosses (edgeComponent e) v) :
    0 < inner ℝ (V.signedVector (V.bankCode (G.sourceFace e))) (sourceNormal e) := by
  have hc := V.crossing_source_label hcut hUV e he heY hcross
  by_cases hlabel : V.faceLabel (G.sourceFace e)=V.positiveLabel
  · simp only [signedVector,bankCode,hlabel,decide_true,↓reduceIte]
    rcases hc with h | h
    · exact h.1
    · exact False.elim (V.labels_ne (hlabel.symm.trans h.2))
  · simp only [signedVector,bankCode,hlabel,decide_false,Bool.false_eq_true,↓reduceIte,inner_neg_left]
    rcases hc with h | h
    · exact False.elim (hlabel h.2)
    · linarith [h.1]

theorem crossing_signed_normal_cone (hcut : cut∈G.ordinaryTrackComponents)
    (hUV : ComponentCrosses cut v) (e : OrientedEdge G) (he : SpineSource e)
    (heY : G.sourceFace e∈B.bankDefectFamily ht side)
    (hcross : ComponentCrosses (edgeComponent e) v) :
    Real.sqrt 3/2 < inner ℝ (V.signedVector (V.bankCode (G.sourceFace e))) (sourceNormal e) := by
  have habs := crossing_port_normal_abs_gt_sqrt_three_half ht v e ((componentGraph G ht).adj_symm hcross)
  have heq := (V.signedVector_sameLine (V.bankCode (G.sourceFace e))).abs_inner_eq
    (SameLine.refl (sourceNormal e))
  rw [← heq,abs_of_pos (V.crossing_signed_normal_pos hcut hUV e he heY hcross)] at habs
  exact habs

include V

theorem sector_ports (hcut : cut∈G.ordinaryTrackComponents) (hUV : ComponentCrosses cut v)
    (hnot : v∉B.bankAnchorTracks ht side) :
    Nonempty (HalfSectorPorts G ht cut v (B.bankDefectFamily ht side) Bool) := by
  let direction (code : Bool) := -(B.signedVector side+V.signedVector code)
  have hangle (code : Bool) : |inner ℝ (B.signedVector side) (V.signedVector code)|<1/2 := by
    rw [(B.signedVector_sameLine side).abs_inner_eq (V.signedVector_sameLine code)]
    exact component_crossing_angle ht hUV
  refine ⟨{
    subset_defects := Finset.filter_subset _ _
    code := V.bankCode
    direction := direction
    direction_ne_zero := fun code => neg_ne_zero.mpr (unit_bisector_ne_zero _ _
      (B.signedVector_norm side) (V.signedVector_norm code) (abs_lt.mp (hangle code)).1)
    missing := ?_
    same_code := ?_ }⟩
  · intro F hF e he hpositive
    have he' := (Finset.mem_filter.mp he).2
    have heY : G.sourceFace e∈B.bankDefectFamily ht side := he'.2 ▸ hF
    have heDef := (Finset.mem_filter.mp heY).1
    have hside := (Finset.mem_filter.mp heY).2
    rw [← he'.2] at hpositive
    have hforbid := opposite_bisector_misses_two_unit_cones
      (B.signedVector side) (V.signedVector (V.bankCode (G.sourceFace e))) (sourceNormal e)
      (B.signedVector_norm side) (V.signedVector_norm _) (sourceNormal_norm e)
      (abs_lt.mp (hangle (V.bankCode (G.sourceFace e)))).1 hpositive
    constructor
    · intro hU
      have h := B.crossing_signed_normal_cone ht e he'.1 heDef ((componentGraph G ht).adj_symm hU)
      rw [hside] at h
      linarith [hforbid.1]
    · intro hV
      have h := V.crossing_signed_normal_cone hcut hUV e he'.1 heY ((componentGraph G ht).adj_symm hV)
      linarith [hforbid.2]
  · intro e f he heY hf hfY hc hmu hmv
    have heF := (Finset.mem_filter.mp heY).1
    have hfF := (Finset.mem_filter.mp hfY).1
    have hnu := defect_source_component_ne_ordinary ht e he heF cut hcut
    have hnv : edgeComponent e≠v := by
      intro heq
      apply hnot
      rw [← heq]
      exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heY⟩,rfl⟩
    have hlabels := G.noncrossing_two_spine_source_labels_eq ht cut v B.outer B.outer_unbounded
      V.loop V.support e f he hf heF hfF hc.symm hnu hnv
      (fun h => hmu ((componentGraph G ht).adj_symm h))
      (fun h => hmv ((componentGraph G ht).adj_symm h))
    exact congrArg (fun z : ℤ => decide (z=V.positiveLabel)) hlabels

end HalfLocalBankData

end Swanepoel
