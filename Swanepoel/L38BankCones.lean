module
public import Swanepoel.L38BankFamilies
public import Swanepoel.UnitCircleSharpIntervals
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem exists_sharp_bank_cone_axes (v : Plane) (hv : ‖v‖=1) :
    ∃ axis : Bool→Plane,(∀ b,‖axis b‖=1) ∧ |inner ℝ (axis false) (axis true)|≤1/2 ∧
      ∀ x : Plane,‖x‖=1 → Real.sqrt 3/2 < inner ℝ v x → twoConeSlots axis x=2 := by
  obtain ⟨ρ,hρ⟩ := exists_unitAngleVector v hv
  let axis (b : Bool) := unitAngleVector (ρ+(if b then (1/2:ℝ) else -1/2))
  refine ⟨axis,fun b => unitAngleVector_norm _,?_,?_⟩
  · change |inner ℝ (unitAngleVector (ρ+(-1/2))) (unitAngleVector (ρ+1/2))|≤1/2
    rw [unitAngleVector_inner,show (ρ+1/2)-(ρ+(-1/2))=(1:ℝ) by ring,mul_one,Real.cos_pi_div_three]
    norm_num
  · intro x hx hsharp
    obtain ⟨θ,hθ,hphase⟩ := exists_relative_unitAngleVector x hx ρ (-3)
    have hcos : Real.sqrt 3/2<Real.cos (Real.pi/3*θ) := by
      rw [← hρ,← hphase,unitAngleVector_inner,add_sub_cancel_left] at hsharp
      exact hsharp
    have hsmall := cos_sharp_phase_abs_lt_half θ (by
      rw [abs_le]
      constructor <;> linarith [hθ.1,hθ.2]) hcos
    have hlo := (abs_lt.mp hsmall).1
    have hhi := (abs_lt.mp hsmall).2
    have hleft : HalfOpen120Cone (axis false) x := by
      rw [← hphase]
      apply unitAngleVector_half_open
      constructor <;> dsimp [axis] <;> linarith only [hlo,hhi]
    have hright : HalfOpen120Cone (axis true) x := by
      rw [← hphase]
      apply unitAngleVector_half_open
      constructor <;> dsimp [axis] <;> linarith only [hlo,hhi]
    simp only [twoConeSlots,ite_eq_left hleft,ite_eq_left hright]

theorem PennyGraph.partial_join_slots_pos {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (axis : Bool→Plane)
    (haxis : ∀ b,‖axis b‖=1) (hsep : |inner ℝ (axis false) (axis true)|≤1/2)
    (c : TrackComponent G) (hc : c∈G.partialInternalJoins Y) :
    1≤∑ e∈G.familyPortFiber Y c,twoConeSlots axis (sourceNormal e) := by
  obtain ⟨e,f,hne,hpair⟩ := Finset.card_eq_two.mp (G.partial_internal_join_fiber_card ht Y c hc)
  have he : e∈G.familyPortFiber Y c := by rw [hpair]; simp
  have hf : f∈G.familyPortFiber Y c := by rw [hpair]; simp
  have he' := Finset.mem_filter.mp he
  have hf' := Finset.mem_filter.mp hf
  have hcomp := hf'.2.trans he'.2.symm
  have hn := source_normals_opposite ht (Finset.mem_filter.mp he'.1).2.1
    (Finset.mem_filter.mp hf'.1).2.1 hcomp (Ne.symm hne)
  rw [hpair,Finset.sum_pair hne,hn]
  exact twoConeSlots_antipodal_cover axis (sourceNormal e) haxis (sourceNormal_norm e) hsep

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem subfamily_two_cone_axes (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    ∃ axis : Bool→Plane,(∀ b,‖axis b‖=1) ∧ |inner ℝ (axis false) (axis true)|≤1/2 ∧
      ∀ e∈B.subfamilyMeetingPorts Y,twoConeSlots axis (sourceNormal e)=2 := by
  obtain ⟨axis,hnorm,hsep,hsharp⟩ := exists_sharp_bank_cone_axes (B.signedVector side) (B.signedVector_norm side)
  refine ⟨axis,hnorm,hsep,?_⟩
  intro e he
  have hep := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have heBank := hY hep.2
  have hc := B.crossing_signed_normal_cone ht e hep.1 (Finset.mem_filter.mp heBank).1
    ((componentGraph G ht).adj_symm (Finset.mem_filter.mp he).2)
  rw [(Finset.mem_filter.mp heBank).2] at hc
  exact hsharp (sourceNormal e) (sourceNormal_norm e) hc

theorem subfamily_slots_lower (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side)
    (axis : Bool→Plane) (haxis : ∀ b,‖axis b‖=1)
    (hsep : |inner ℝ (axis false) (axis true)|≤1/2)
    (hcross : ∀ e∈B.subfamilyMeetingPorts Y,twoConeSlots axis (sourceNormal e)=2) :
    2*(B.subfamilyMeetingPorts Y).card+(G.partialInternalJoins Y).card≤
      ∑ e∈G.familySourcePorts Y,twoConeSlots axis (sourceNormal e) := by
  let P := B.subfamilyMeetingPorts Y
  let Q := G.familySourcePorts Y
  let J := G.partialInternalJoins Y
  let slot (e : OrientedEdge G) := twoConeSlots axis (sourceNormal e)
  have hlocal (c : TrackComponent G) (hc : c∈G.familyTrackComponents Y) :
      2*(P.filter (fun e => edgeComponent e=c)).card+(if c∈J then 1 else 0)≤
        ∑ e∈G.familyPortFiber Y c,slot e := by
    by_cases hcJ : c∈J
    · have hempty : P.filter (fun e => edgeComponent e=c)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have he' := Finset.mem_filter.mp he
        have hUnp := B.subfamilyMeetingPorts_subset_unpaired ht side Y hY he'.1
        have hUnpComp := (Finset.mem_filter.mp hUnp).2
        rw [he'.2] at hUnpComp
        exact (Finset.mem_sdiff.mp hcJ).2 hUnpComp
      rw [hempty,Finset.card_empty,mul_zero,zero_add,ite_eq_left hcJ]
      exact G.partial_join_slots_pos ht Y axis haxis hsep c hcJ
    · rw [ite_eq_right hcJ,add_zero]
      have hsub : P.filter (fun e => edgeComponent e=c)⊆G.familyPortFiber Y c := by
        intro e he
        have he' := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he'.1).1,he'.2⟩
      calc
        _ = ∑ e∈P.filter (fun e => edgeComponent e=c),slot e := by
          have hs : (∑ e∈P.filter (fun e => edgeComponent e=c),slot e)=
              ∑ _∈P.filter (fun e => edgeComponent e=c),2 := by
            apply Finset.sum_congr rfl
            intro e he
            exact hcross e (Finset.mem_filter.mp he).1
          rw [hs]
          simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hP : P.card=∑ c∈G.familyTrackComponents Y,(P.filter (fun e => edgeComponent e=c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => Finset.mem_image.mpr
      ⟨e,(Finset.mem_filter.mp he).1,rfl⟩)
  have hJ : (∑ c∈G.familyTrackComponents Y,if c∈J then 1 else 0)=J.card := by
    have hsub : J⊆G.familyTrackComponents Y := Finset.sdiff_subset
    calc
      _ = ∑ c∈J,if c∈J then 1 else 0 :=
        (Finset.sum_subset hsub (fun c _ hn => by rw [ite_eq_right hn])).symm
      _ = _ := by simp
  have hsum := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← hP,hJ] at hsum
  have hfib := Finset.sum_fiberwise_of_maps_to
    (fun e he => Finset.mem_image.mpr ⟨e,he,rfl⟩ : ∀ e∈Q,edgeComponent e∈G.familyTrackComponents Y) slot
  change (∑ c∈G.familyTrackComponents Y,∑ e∈G.familyPortFiber Y c,slot e)=∑ e∈Q,slot e at hfib
  rwa [hfib] at hsum

theorem subfamily_restriction_four (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    2*((B.subfamilyMeetingPorts Y).card : ℤ)≤G.familyPortExcess Y+G.familyK Y := by
  obtain ⟨axis,hnorm,hsep,hcross⟩ := B.subfamily_two_cone_axes ht side Y hY
  have hlo := B.subfamily_slots_lower ht side Y hY axis hnorm hsep hcross
  have htotal : (∑ e∈G.familySourcePorts Y,twoConeSlots axis (sourceNormal e))+6*Y.card≤
      2*(G.familySourcePorts Y).card := by
    have hsum := Finset.sum_le_sum (fun F hF => G.two_cone_slots_face_bound ht F
      (Finset.mem_filter.mp (hY hF)).1 hdegree axis hnorm)
    have hfib := Finset.sum_fiberwise_of_maps_to
      (fun e he => (Finset.mem_filter.mp he).2.2 : ∀ e∈G.familySourcePorts Y,G.sourceFace e∈Y)
      (fun e => twoConeSlots axis (sourceNormal e))
    have hface (F : PlaneFace G) (hF : F∈Y) :
        (G.familySourcePorts Y).filter (fun e => G.sourceFace e=F)=G.faceSourcePorts F := by
      ext e
      simp only [PennyGraph.familySourcePorts,PennyGraph.faceSourcePorts,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2 ▸ hF⟩,h.2⟩⟩
    rw [G.familySourcePorts_card,← hfib]
    have hfaceSum : (∑ F∈Y,∑ e∈(G.familySourcePorts Y).filter (fun e => G.sourceFace e=F),
        twoConeSlots axis (sourceNormal e))=
        ∑ F∈Y,∑ e∈G.faceSourcePorts F,twoConeSlots axis (sourceNormal e) := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [hface F hF]
    rw [hfaceSum]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,Finset.mul_sum,Nat.mul_comm] using hsum
  have hcount : 2*(B.subfamilyMeetingPorts Y).card+(G.partialInternalJoins Y).card+6*Y.card≤
      2*(G.familySourcePorts Y).card := by omega
  have hZ : 2*((B.subfamilyMeetingPorts Y).card : ℤ)+(G.partialInternalJoins Y).card+6*Y.card≤
      2*(G.familySourcePorts Y).card := by exact_mod_cast hcount
  have hid := G.partial_family_bank_identities ht Y
  omega

end OrdinaryCutBanks
end Swanepoel
