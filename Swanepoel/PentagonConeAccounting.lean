module
public import Swanepoel.SpokePairTransport
public import Swanepoel.JoinSlotCounting
public import Swanepoel.HalfOpenAntipodalCover
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def twoConeSlots (axis : Bool→Plane) (normal : Plane) : ℕ :=
  (if HalfOpen120Cone (axis false) normal then 1 else 0)+
    (if HalfOpen120Cone (axis true) normal then 1 else 0)

theorem twoConeSlots_antipodal_cover (axis : Bool→Plane) (x : Plane)
    (haxis : ∀ b, ‖axis b‖=1) (hx : ‖x‖=1)
    (hab : |inner ℝ (axis false) (axis true)|≤1/2) :
    1≤twoConeSlots axis x+twoConeSlots axis (-x) := by
  have h := half_open_two_cones_antipodal_cover (axis false) (axis true) x
    (haxis false) (haxis true) hx hab
  unfold twoConeSlots
  split_ifs <;> simp_all

theorem PennyGraph.two_cone_slots_face_bound {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (H : PlaneFace G) (hH : H∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (axis : Bool→Plane) (haxis : ∀ b,‖axis b‖=1) :
    (∑ e∈G.faceSourcePorts H,twoConeSlots axis (sourceNormal e))+6≤2*(G.faceSourcePorts H).card := by
  have h0 := G.defect_half_open_120_cone_count ht H hH hdegree (axis false) (haxis false)
  have h1 := G.defect_half_open_120_cone_count ht H hH hdegree (axis true) (haxis true)
  have heq : (∑ e∈G.faceSourcePorts H,twoConeSlots axis (sourceNormal e))=
      ((G.faceSourcePorts H).filter (fun e => HalfOpen120Cone (axis false) (sourceNormal e))).card+
      ((G.faceSourcePorts H).filter (fun e => HalfOpen120Cone (axis true) (sourceNormal e))).card := by
    simp only [twoConeSlots,Finset.sum_add_distrib,Finset.card_eq_sum_ones,Finset.sum_filter]
  omega

theorem PentagonSpokeLoops.mixed_bound_of_cone_assignment {n : ℕ} {G : PennyGraph n}
    {F : PlaneFace G} {P : PentagonFaceBoundary G F} (K : PentagonSpokeLoops G F P)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (axis : (Fin 5→ℤ)→Bool→Plane) (haxis : ∀ code b,‖axis code b‖=1)
    (hantipodal : ∀ code x,‖x‖=1 → 1≤twoConeSlots (axis code) x+twoConeSlots (axis code) (-x))
    (hcapacity : ∀ e∈G.familySourcePorts (Y\{F}),
      G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)≤
        twoConeSlots (axis (K.code (G.sourceFace e))) (sourceNormal e)) :
    (G.interFamilyCrossings ht {F} (Y\{F}) : ℤ)+G.familyJoinCount (Y\{F})≤
      2*((G.familySourcePorts (Y\{F})).card : ℤ)-6*(Y\{F}).card := by
  let Z := Y\{F}
  have hZ : G.IsJoinClosed ht Z := hY.sdiff (G.boundary_face_singleton_joinClosed ht hY F hFY hports)
  let slot (e : OrientedEdge G) := twoConeSlots (axis (K.code (G.sourceFace e))) (sourceNormal e)
  have hport (i : Fin 5) : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hsilent (c : TrackComponent G) (hc : c∈G.familyJoinTrackComponents Z)
      (hz : G.familyCrossingDegree (G.familyTrackComponents {F}) c=0) :
      1≤∑ e∈G.familyPortFiber Z c,slot e := by
    obtain ⟨e,f,hne,hpair⟩ := Finset.card_eq_two.mp (G.join_port_fiber_card_two ht hZ c hc)
    have he : e∈G.familyPortFiber Z c := by rw [hpair]; simp
    have hf : f∈G.familyPortFiber Z c := by rw [hpair]; simp
    have he' := Finset.mem_filter.mp he
    have hf' := Finset.mem_filter.mp hf
    have hePort := (Finset.mem_filter.mp he'.1).2
    have hfPort := (Finset.mem_filter.mp hf'.1).2
    have heDef := hZ.subset_defects hePort.2
    have hfDef := hZ.subset_defects hfPort.2
    have heRoot : G.sourceFace e≠F := by
      intro h
      exact (Finset.mem_sdiff.mp hePort.2).2 (Finset.mem_singleton.mpr h)
    have hfRoot : G.sourceFace f≠F := by
      intro h
      exact (Finset.mem_sdiff.mp hfPort.2).2 (Finset.mem_singleton.mpr h)
    have hcomp := hf'.2.trans he'.2.symm
    have hmiss (i : Fin 5) : ¬ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i)) := by
      intro hx
      have hA : edgeComponent (P.dart i)∈G.familyTrackComponents {F} := by
        rw [PennyGraph.familyTrackComponents,G.familySourcePorts_singleton]
        exact Finset.mem_image.mpr ⟨P.dart i,hport i,rfl⟩
      have hx' : ComponentCrosses (edgeComponent (P.dart i)) c := by
        rw [← he'.2]
        exact (componentGraph G ht).adj_symm hx
      have hempty : ((G.familyTrackComponents {F}).filter (fun a => ComponentCrosses a c))=∅ :=
        Finset.card_eq_zero.mp hz
      have hmem : edgeComponent (P.dart i)∈
          (G.familyTrackComponents {F}).filter (fun a => ComponentCrosses a c) :=
        Finset.mem_filter.mpr ⟨hA,hx'⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    have hcode := K.zero_crossing_join_code_eq ht hY hFY hports e f heDef hfDef heRoot hfRoot hcomp hmiss
    have hn := source_normals_opposite ht hePort.1 hfPort.1 hcomp (Ne.symm hne)
    rw [hpair,Finset.sum_pair hne]
    change 1≤twoConeSlots (axis (K.code (G.sourceFace e))) (sourceNormal e)+
      twoConeSlots (axis (K.code (G.sourceFace f))) (sourceNormal f)
    rw [← hcode,hn]
    exact hantipodal _ _ (sourceNormal_norm e)
  have hcount := G.mixed_crossings_add_joins_le_slots ht {F} hZ slot hcapacity hsilent
  have htotal : (∑ H∈Z,∑ e∈G.faceSourcePorts H,twoConeSlots (axis (K.code H)) (sourceNormal e))=
      ∑ e∈G.familySourcePorts Z,slot e := by
    have hfib := Finset.sum_fiberwise_of_maps_to
      (fun e he => (Finset.mem_filter.mp he).2.2 : ∀ e∈G.familySourcePorts Z,G.sourceFace e∈Z) slot
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro H hH
    have hset : (G.familySourcePorts Z).filter (fun e => G.sourceFace e=H)=G.faceSourcePorts H := by
      ext e
      simp only [PennyGraph.familySourcePorts,PennyGraph.faceSourcePorts,Finset.mem_filter,
        Finset.mem_univ,true_and]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2 ▸ hH⟩,h.2⟩⟩
    rw [hset]
    exact Finset.sum_congr rfl (fun e he => by
      dsimp only [slot]
      rw [(Finset.mem_filter.mp he).2.2])
  have hsum := Finset.sum_le_sum (fun H hH =>
    G.two_cone_slots_face_bound ht H (hZ.subset_defects hH) hdegree (axis (K.code H)) (haxis _))
  have hupper : (∑ e∈G.familySourcePorts Z,slot e)+6*Z.card≤2*(G.familySourcePorts Z).card := by
    rw [G.familySourcePorts_card]
    rw [← htotal]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,Finset.mul_sum,Nat.mul_comm] using hsum
  have hnat : G.interFamilyCrossings ht {F} Z+G.familyJoinCount Z+6*Z.card≤2*(G.familySourcePorts Z).card := by omega
  have hint : (G.interFamilyCrossings ht {F} Z : ℤ)+G.familyJoinCount Z+6*(Z.card : ℤ)≤
      2*((G.familySourcePorts Z).card : ℤ) := by exact_mod_cast hnat
  change (G.interFamilyCrossings ht {F} Z : ℤ)+G.familyJoinCount Z≤
    2*((G.familySourcePorts Z).card : ℤ)-6*Z.card
  omega

theorem PentagonSpokeLoops.mixed_bound_of_separated_cones {n : ℕ} {G : PennyGraph n}
    {F : PlaneFace G} {P : PentagonFaceBoundary G F} (K : PentagonSpokeLoops G F P)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (axis : (Fin 5→ℤ)→Bool→Plane) (haxis : ∀ code b,‖axis code b‖=1)
    (hseparated : ∀ code, |inner ℝ (axis code false) (axis code true)|≤1/2)
    (hcapacity : ∀ e∈G.familySourcePorts (Y\{F}),
      G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)≤
        twoConeSlots (axis (K.code (G.sourceFace e))) (sourceNormal e)) :
    (G.interFamilyCrossings ht {F} (Y\{F}) : ℤ)+G.familyJoinCount (Y\{F})≤
      2*((G.familySourcePorts (Y\{F})).card : ℤ)-6*(Y\{F}).card := by
  exact K.mixed_bound_of_cone_assignment ht hY hFY hports hdegree axis haxis
    (fun code x hx => twoConeSlots_antipodal_cover (axis code) x (haxis code) hx (hseparated code))
    hcapacity

end Swanepoel
