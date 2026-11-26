module
public import Swanepoel.L38HalfPentagonMixed
public import Swanepoel.L38HalfPentagonFamilyCounts
public import Swanepoel.L38HalfPentagonComponents
public import Swanepoel.L38HalfPentagonRealization
public import Swanepoel.L38HalfAreaJoinClosure
public import Swanepoel.L38HalfAreaInduction
public import Swanepoel.L38HalfConnectivity
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.l38_pentagons_internal_of_boundaries {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {W A : Finset (PlaneFace G)} (hW : G.IsJoinClosed ht W) (hAW : A⊆W)
    (hports : ∀ F∈A,∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents W)
    (ρ : ℝ) (hbins : ∀ F∈A,∃ P : PentagonFaceBoundary G F,Nonempty (P.BankBinData ρ)) :
    2*(G.familyInternalCrossings ht A : ℤ)≤3*(A.card : ℤ)*(A.card-1) := by
  induction A using Finset.induction_on with
  | empty =>
    have hz : G.familyInternalCrossings ht ∅=0 := by
      unfold PennyGraph.familyInternalCrossings
      rw [G.l38_familyTrackIndices_empty]
      exact TrackSystem.l38_internal_empty _
    rw [hz]
    norm_num
  | @insert F A hFA ih =>
    have hsub : A⊆insert F A := Finset.subset_insert _ _
    have hAW' := hsub.trans hAW
    have hpA := fun H hH => hports H (hsub hH)
    have hAc := G.l38_isolated_subfamily_closed ht hW hAW' hpA
    have hFW := hAW (Finset.mem_insert_self _ _)
    have hpF := hports F (Finset.mem_insert_self _ _)
    have hFc := G.boundary_face_singleton_joinClosed ht hW F hFW hpF
    have hsingle (H) (hH : H∈A) :=
      G.boundary_face_singleton_joinClosed ht hW H (hAW' hH) (hpA H hH)
    have hrec := ih hAW' hpA (fun H hH => hbins H (hsub hH))
    obtain ⟨P,⟨D⟩⟩ := hbins F (Finset.mem_insert_self _ _)
    have hcross : G.interFamilyCrossings ht {F} A≤3*A.card := by
      rw [G.l38_crossings_sum_singletons_right ht {F} A hsingle]
      calc
        _ ≤ ∑ _∈A,3 := Finset.sum_le_sum (fun H hH => by
          obtain ⟨Q,⟨E⟩⟩ := hbins H (hsub hH)
          exact G.isolated_pentagon_pair_crossings_le_three_of_bins ht hW P Q hFW (hAW' hH)
            (by intro h; exact hFA (h ▸ hH)) hpF (hpA H hH) D E)
        _ = 3*A.card := by simp [Nat.mul_comm]
    have hsplit := G.family_internal_crossings_union ht hFc hAc (by simpa using hFA)
    rw [show {F}∪A=insert F A by ext H; simp,
      P.internal_crossings_zero ht (hW.subset_defects hFW),zero_add] at hsplit
    rw [hsplit,Finset.card_insert_of_notMem hFA]
    have hcross' : (G.interFamilyCrossings ht {F} A : ℤ)≤3*(A.card : ℤ) := by exact_mod_cast hcross
    push_cast
    nlinarith only [hrec,hcross']

theorem PennyGraph.l38_pentagons_X_of_boundaries {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {W A : Finset (PlaneFace G)} (hW : G.IsJoinClosed ht W) (hAW : A⊆W)
    (hports : ∀ F∈A,∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents W)
    (ρ : ℝ) (hbins : ∀ F∈A,∃ P : PentagonFaceBoundary G F,Nonempty (P.BankBinData ρ)) :
    (G.familyInternalCrossings ht A : ℝ)+A.card≤3*(A.card : ℝ)^2/2 := by
  have h := G.l38_pentagons_internal_of_boundaries ht hW hAW hports ρ hbins
  have hr : 2*(G.familyInternalCrossings ht A : ℝ)≤3*(A.card : ℝ)*(A.card-1) := by exact_mod_cast h
  nlinarith only [hr,show (0:ℝ)≤A.card by positivity]

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem half_pentagon_crossing_estimate (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.halfGraph side).PentagonCrossingEstimate (B.halfGraph_triangleFree ht side) :=
  B.half_pentagon_crossing_estimate_of_bank_faces ht side hdegree
    (B.half_defect_bank_face_surjective ht hc hcut side)

theorem half_five_port_internal_zero (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (K : PlaneFace (B.halfGraph side))
    (hK : K∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side))
    (hfive : ((B.halfGraph side).faceSourcePorts K).card=5) :
    (B.halfGraph side).familyInternalCrossings (B.halfGraph_triangleFree ht side) {K}=0 := by
  obtain ⟨F,hF,rfl⟩ := B.half_defect_bank_face_surjective ht hc hcut side K hK
  have hfiveOld : (G.faceSourcePorts F).card=5 := by
    rwa [B.bankDefect_sourcePorts_card ht side F hF] at hfive
  obtain ⟨P⟩ := G.five_port_face_boundary ht F (Finset.mem_filter.mp hF).1 hdegree hfiveOld
  exact (B.bankPentagonBoundary ht side F hF P).internal_crossings_zero
    (B.halfGraph_triangleFree ht side) (B.bankDefectPlaneFace_mem_defects ht side F hF)

theorem canonicalHalf_quadratic (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalHalfTracks ht side).QuadraticBound :=
  (B.halfGraph side).canonical_quadratic_of_local_five_port_geometry
    (B.halfGraph_triangleFree ht side) (B.halfGraph_connected ht hc side)
    (B.half_defect_area_lower ht hc hcut side hdegree)
    (B.half_pentagon_crossing_estimate ht hc hdegree hcut side)
    (B.half_five_port_internal_zero ht hc hdegree hcut side)

theorem bank_family_quadratic (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    10000*G.familyR ht (B.bankDefectFamily ht side)≤2379*(G.familyK (B.bankDefectFamily ht side))^2 := by
  have hq := (B.halfGraph side).family_quadratic_of_local_five_port_geometry
    (B.halfGraph_triangleFree ht side) (B.halfGraph_connected ht hc side)
    (B.half_defect_area_lower ht hc hcut side hdegree)
    (B.half_pentagon_crossing_estimate ht hc hdegree hcut side)
    (B.half_five_port_internal_zero ht hc hdegree hcut side)
    ((B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side))
    ((B.halfGraph side).joinClosed_all_defects (B.halfGraph_triangleFree ht side))
  rw [← B.bankDefectImage_all ht hc hcut side,B.bankDefectImage_R ht side _ _,
    B.bankDefectImage_K ht side _ _] at hq
  exact hq

theorem bank_isolated_pair_crossings_le_three (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (F K : PlaneFace G) (hF : F∈B.isolatedTwoPortPentagons ht side)
    (hK : K∈B.isolatedTwoPortPentagons ht side) (hne : K≠F) :
    G.interFamilyCrossings ht {F} {K}≤3 := by
  obtain ⟨ρ,_,hlocal⟩ := B.exists_isolated_bank_bin_boundaries ht hdegree side
  obtain ⟨P,⟨D⟩⟩ := hlocal F hF
  obtain ⟨Q,⟨E⟩⟩ := hlocal K hK
  let hFB := (Finset.mem_filter.mp hF).1
  let hKB := (Finset.mem_filter.mp hK).1
  have hneHalf : B.bankDefectPlaneFace ht side K hKB≠B.bankDefectPlaneFace ht side F hFB := by
    intro h
    exact hne (Subtype.ext (congrArg (fun L : PlaneFace (B.halfGraph side) => L.val) h))
  have hp := (B.halfGraph side).isolated_pentagon_pair_crossings_le_three_of_bins
    (B.halfGraph_triangleFree ht side)
    ((B.halfGraph side).joinClosed_all_defects (B.halfGraph_triangleFree ht side))
    (B.bankPentagonBoundary ht side F hFB P) (B.bankPentagonBoundary ht side K hKB Q)
    (B.bankDefectPlaneFace_mem_defects ht side F hFB) (B.bankDefectPlaneFace_mem_defects ht side K hKB)
    hneHalf
    (B.isolated_pentagon_half_boundary_ports ht side (B.half_defect_bank_face_surjective ht hc hcut side) F hF)
    (B.isolated_pentagon_half_boundary_ports ht side (B.half_defect_bank_face_surjective ht hc hcut side) K hK)
    (B.bankPentagonBins ht side F hFB P D) (B.bankPentagonBins ht side K hKB Q E)
  have hm := B.bankDefectImage_inter_crossings ht side {F} {K}
    (Finset.singleton_subset_iff.mpr hFB) (Finset.singleton_subset_iff.mpr hKB)
  rw [B.bankDefectImage_singleton,B.bankDefectImage_singleton] at hm
  rw [← hm]
  exact hp

theorem bank_isolated_X_bound (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (G.familyInternalCrossings ht (B.isolatedTwoPortPentagons ht side) : ℝ)+
      (B.isolatedTwoPortPentagons ht side).card≤3*((B.isolatedTwoPortPentagons ht side).card : ℝ)^2/2 := by
  have hS : B.isolatedTwoPortPentagons ht side⊆B.bankDefectFamily ht side := Finset.filter_subset _ _
  let H := B.halfGraph side
  let A := B.halfIsolatedDefects ht side
  obtain ⟨ρ,_,hlocal⟩ := B.exists_isolated_bank_bin_boundaries ht hdegree side
  have hbins : ∀ F∈A,∃ P : PentagonFaceBoundary H F,Nonempty (P.BankBinData ρ) := by
    intro F hF
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨P,⟨D⟩⟩ := hlocal K.val K.property
    exact ⟨B.bankPentagonBoundary ht side K.val (hS K.property) P,
      ⟨B.bankPentagonBins ht side K.val (hS K.property) P D⟩⟩
  have hX := H.l38_pentagons_X_of_boundaries (B.halfGraph_triangleFree ht side)
    (H.joinClosed_all_defects (B.halfGraph_triangleFree ht side))
    (B.bankDefectImage_subset_defects ht side _ _) (B.half_isolated_ports_boundary ht hc hcut side) ρ hbins
  change (H.familyInternalCrossings (B.halfGraph_triangleFree ht side)
    (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hS) : ℝ)+
      (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hS).card≤
        3*((B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hS).card : ℝ)^2/2 at hX
  dsimp only [H] at hX
  rw [B.bankDefectImage_internal_crossings ht side _ _,B.bankDefectImage_card ht side _ _] at hX
  exact hX

theorem bank_isolated_M_bound (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (G.interFamilyCrossings ht (B.isolatedTwoPortPentagons ht side) (B.bankRemainder ht side) : ℤ)≤
      ((B.isolatedTwoPortPentagons ht side).card : ℤ)*
        (G.familyK (B.bankRemainder ht side)+G.familyPortExcess (B.bankRemainder ht side)) := by
  have hS : B.isolatedTwoPortPentagons ht side⊆B.bankDefectFamily ht side := Finset.filter_subset _ _
  let H := B.halfGraph side
  let hH := B.halfGraph_triangleFree ht side
  let A := B.halfIsolatedDefects ht side
  let Z := B.halfRemainderDefects ht side
  let W := H.defectPlaneFaces hH
  have hW := H.joinClosed_all_defects hH
  have hA : A⊆W := B.bankDefectImage_subset_defects ht side _ _
  have hZ : H.IsJoinClosed hH Z := B.halfRemainderDefects_joinClosed ht hc hcut side
  have hAZ : Disjoint A Z := B.bankDefectImage_disjoint ht side _ _ _ _
    (B.bank_isolated_remainder_disjoint ht side)
  have hpentagon := B.half_pentagon_crossing_estimate ht hc hdegree hcut side
  have hports (F) (hF : F∈A) := B.half_isolated_ports_boundary ht hc hcut side F hF
  have hsingle (F) (hF : F∈A) := H.boundary_face_singleton_joinClosed hH hW F (hA hF) (hports F hF)
  have hpoint (F) (hF : F∈A) :
      (H.interFamilyCrossings hH {F} Z : ℤ)≤H.familyK Z+H.familyPortExcess Z := by
    have hFZ : F∉Z := fun h => Finset.disjoint_left.mp hAZ hF h
    have hrest : ({F}∪Z)\{F}=Z := by
      ext L
      by_cases h : L=F
      · subst L
        simp [hFZ]
      · simp [h]
    have hfive : (H.faceSourcePorts F).card=5 := by
      obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hF
      rw [B.bankDefect_sourcePorts_card ht side K.val (hS K.property)]
      exact (Finset.mem_filter.mp K.property).2.1
    have hp (e) (he : e∈H.faceSourcePorts F) : edgeComponent e∈H.familyBoundaryTrackComponents ({F}∪Z) := by
      have hes := (Finset.mem_filter.mp he).2
      apply H.l38_boundary_port_transfer e hes.1
      · rw [hes.2]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      · exact hports F hF e he
    have hm := hpentagon ({F}∪Z) ((hsingle F hF).union hZ) F
      (Finset.mem_union_left _ (Finset.mem_singleton_self _)) hfive hp
    rw [hrest] at hm
    change (H.interFamilyCrossings hH {F} Z : ℤ)+H.familyJoinCount Z≤
      2*((H.familySourcePorts Z).card : ℤ)-6*Z.card at hm
    have htrack := H.family_tracks_boundary_add_joins hH hZ
    have hport := H.family_ports_boundary_add_twice_joins hH hZ
    rw [← H.familySourcePorts_card] at hport
    have hex : H.familyPortExcess Z=(H.familySourcePorts Z).card-4*Z.card := by
      rw [H.familyPortExcess_eq,H.familySourcePorts_card,Nat.cast_sum]
    unfold PennyGraph.familyK
    omega
  have hM : (H.interFamilyCrossings hH A Z : ℤ)≤(A.card : ℤ)*(H.familyK Z+H.familyPortExcess Z) := by
    rw [H.l38_crossings_sum_singletons_left hH A Z hsingle,Nat.cast_sum]
    calc
      _ ≤ ∑ _∈A,(H.familyK Z+H.familyPortExcess Z) := Finset.sum_le_sum (fun F hF => hpoint F hF)
      _ = _ := by simp [mul_comm]
  change ((H.interFamilyCrossings hH
    (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hS)
    (B.bankDefectImage ht side (B.bankRemainder ht side) (B.bankRemainder_subset ht side))) : ℤ)≤
      ((B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hS).card : ℤ)*
        (H.familyK (B.bankDefectImage ht side (B.bankRemainder ht side) (B.bankRemainder_subset ht side))+
          H.familyPortExcess (B.bankDefectImage ht side (B.bankRemainder ht side) (B.bankRemainder_subset ht side))) at hM
  dsimp only [H,hH] at hM
  rw [B.bankDefectImage_inter_crossings ht side _ _ _ _,B.bankDefectImage_card ht side _ _,
    B.bankDefectImage_K ht side _ _,B.bankDefectImage_portExcess ht side _ _] at hM
  exact hM

end OrdinaryCutBanks
end Swanepoel
