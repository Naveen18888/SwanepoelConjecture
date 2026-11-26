module
public import Swanepoel.CrossingSourceBanks
public import Swanepoel.SectorPortCounting
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def bankCode (F : PlaneFace G) : Bool := decide (B.faceLabel F=B.positiveLabel)
def signedVector (code : Bool) : Plane := if code then B.vector else -B.vector

theorem signedVector_norm (code : Bool) : ‖B.signedVector code‖=1 := by
  cases code <;> simp only [signedVector,Bool.false_eq_true,↓reduceIte,norm_neg,B.vector_norm]

theorem signedVector_sameLine (code : Bool) : SameLine (B.signedVector code) (componentVector cut) := by
  have h := component_sameLine B.start cut B.component
  change SameLine B.vector (componentVector cut) at h
  cases code
  · exact (show SameLine (-B.vector) B.vector from Or.inr rfl).trans h
  · exact h

theorem crossing_signed_normal_pos (ht : G.TriangleFree) (e : OrientedEdge G)
    (he : SpineSource e) (heF : G.sourceFace e∈G.defectPlaneFaces ht)
    (hcross : ComponentCrosses (edgeComponent e) cut) :
    0 < inner ℝ (B.signedVector (B.bankCode (G.sourceFace e))) (sourceNormal e) := by
  have hc := B.crossing_source_label ht e he heF hcross
  by_cases hlabel : B.faceLabel (G.sourceFace e)=B.positiveLabel
  · simp only [signedVector,bankCode,hlabel,decide_true,↓reduceIte]
    rcases hc with h | h
    · exact h.1
    · exact False.elim (B.labels_ne (hlabel.symm.trans h.2))
  · simp only [signedVector,bankCode,hlabel,decide_false,Bool.false_eq_true,↓reduceIte,inner_neg_left]
    rcases hc with h | h
    · exact False.elim (hlabel h.2)
    · linarith [h.1]

theorem crossing_signed_normal_cone (ht : G.TriangleFree) (e : OrientedEdge G)
    (he : SpineSource e) (heF : G.sourceFace e∈G.defectPlaneFaces ht)
    (hcross : ComponentCrosses (edgeComponent e) cut) :
    Real.sqrt 3/2 < inner ℝ (B.signedVector (B.bankCode (G.sourceFace e))) (sourceNormal e) := by
  have hc : ComponentCrosses cut (edgeComponent e) := (componentGraph G ht).adj_symm hcross
  have habs := crossing_port_normal_abs_gt_sqrt_three_half ht cut e hc
  have hsame := B.signedVector_sameLine (B.bankCode (G.sourceFace e))
  have heq := hsame.abs_inner_eq (SameLine.refl (sourceNormal e))
  rw [← heq,abs_of_pos (B.crossing_signed_normal_pos ht e he heF hcross)] at habs
  exact habs

end OrdinaryCutBanks

theorem defect_source_component_ne_ordinary {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (e : OrientedEdge G) (he : SpineSource e)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (cut : TrackComponent G)
    (hord : cut∈G.ordinaryTrackComponents) : edgeComponent e≠cut := by
  intro heq
  have hport : e∈G.faceSourcePorts (G.sourceFace e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,rfl⟩
  have hterm := G.defect_source_port_terminal ht heF hport
  rw [heq] at hterm
  exact (G.mem_terminalTrackComponents cut).mp hterm hord

theorem actual_sector_port_data {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (u v : TrackComponent G) (hu : u∈G.ordinaryTrackComponents)
    (hv : v∈G.ordinaryTrackComponents) (hcross : ComponentCrosses u v) :
    Nonempty (SectorPortData G ht u v (Bool×Bool)) := by
  obtain ⟨U⟩ := exists_ordinaryCutBanks ht u v hu hcross
  obtain ⟨V⟩ := exists_ordinaryCutBanks ht v u hv ((componentGraph G ht).adj_symm hcross)
  let direction (code : Bool×Bool) := -(U.signedVector code.1+V.signedVector code.2)
  have hangle (code : Bool×Bool) : |inner ℝ (U.signedVector code.1) (V.signedVector code.2)|<1/2 := by
    rw [(U.signedVector_sameLine code.1).abs_inner_eq (V.signedVector_sameLine code.2)]
    exact component_crossing_angle ht hcross
  have hdir (code : Bool×Bool) : direction code≠0 := by
    exact neg_ne_zero.mpr (unit_bisector_ne_zero _ _ (U.signedVector_norm code.1)
      (V.signedVector_norm code.2) (abs_lt.mp (hangle code)).1)
  refine ⟨{
    code := fun F => (U.bankCode F,V.bankCode F)
    direction := direction
    direction_ne_zero := hdir
    missing := ?_
    same_code := ?_ }⟩
  · intro F hF e he hpositive
    have he' := (Finset.mem_filter.mp he).2
    have heF : G.sourceFace e∈G.defectPlaneFaces ht := he'.2 ▸ hF
    have hcode : (U.bankCode F,V.bankCode F)=(U.bankCode (G.sourceFace e),V.bankCode (G.sourceFace e)) := by rw [he'.2]
    rw [hcode] at hpositive
    have hforbid := opposite_bisector_misses_two_unit_cones
      (U.signedVector (U.bankCode (G.sourceFace e))) (V.signedVector (V.bankCode (G.sourceFace e)))
      (sourceNormal e) (U.signedVector_norm _) (V.signedVector_norm _) (sourceNormal_norm e)
      (abs_lt.mp (hangle (U.bankCode (G.sourceFace e),V.bankCode (G.sourceFace e)))).1 hpositive
    constructor
    · intro hU
      have h := U.crossing_signed_normal_cone ht e he'.1 heF ((componentGraph G ht).adj_symm hU)
      linarith [hforbid.1]
    · intro hV
      have h := V.crossing_signed_normal_cone ht e he'.1 heF ((componentGraph G ht).adj_symm hV)
      linarith [hforbid.2]
  · intro e f he heF hf hfF hc hmu hmv
    have hnu := defect_source_component_ne_ordinary ht e he heF u hu
    have hnv := defect_source_component_ne_ordinary ht e he heF v hv
    have hU := U.missing_source_face_labels_eq ht e f he hf heF hfF hc.symm hnu
      (fun h => hmu ((componentGraph G ht).adj_symm h))
    have hV := V.missing_source_face_labels_eq ht e f he hf heF hfF hc.symm hnv
      (fun h => hmv ((componentGraph G ht).adj_symm h))
    apply Prod.ext
    · simp only [OrdinaryCutBanks.bankCode,hU]
    · simp only [OrdinaryCutBanks.bankCode,hV]

theorem PennyGraph.canonical_crossing_pair_bound {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).CrossingPairBound := by
  apply G.crossing_pair_bound_of_sector_data ht (Bool×Bool) hdegree
  intro u hu v hv hc
  exact actual_sector_port_data ht u v hu hv hc

end Swanepoel
