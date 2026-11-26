module
public import Swanepoel.L38PentagonPairCrossings
public import Swanepoel.PentagonMixedEstimate
public import Swanepoel.L38BankPartition
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.l38TwoSharpBankPorts {n : ℕ} (G : PennyGraph n) (ρ : ℝ) (F : PlaneFace G) : Prop :=
  ∃ e∈G.faceSourcePorts F,∃ f∈G.faceSourcePorts F,e≠f ∧
    Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (sourceNormal e) ∧
    Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (sourceNormal f)

theorem PennyGraph.l38_bank_bins_of_actual_ports {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hfive : (G.faceSourcePorts F).card=5) (ρ : ℝ) (hbank : G.l38TwoSharpBankPorts ρ F) :
    ∃ P : PentagonFaceBoundary G F,Nonempty (P.BankBinData ρ) := by
  obtain ⟨P⟩ := G.five_port_face_boundary ht F hF hdegree hfive
  obtain ⟨e,he,f,hf,hne,hbe,hbf⟩ := hbank
  rw [← P.darts] at he hf
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hf
  have hi' : P.dart i=e := hi
  have hj' : P.dart j=f := hj
  have hij : i≠j := by
    intro h
    apply hne
    rw [← hi,← hj,h]
  apply P.exists_bank_bin_boundary_of_sharp_pair ht hF ρ i j hij
  · change Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (sourceNormal (P.dart i))
    rw [hi']
    exact hbe
  · change Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (sourceNormal (P.dart j))
    rw [hj']
    exact hbf

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem exists_isolated_two_sharp_bank_ports (ht : G.TriangleFree) (side : Bool) :
    ∃ ρ : ℝ,unitAngleVector (ρ+1/2)=B.signedVector side ∧
      ∀ F∈B.isolatedTwoPortPentagons ht side,G.l38TwoSharpBankPorts ρ F := by
  obtain ⟨τ,hτ⟩ := exists_unitAngleVector (B.signedVector side) (B.signedVector_norm side)
  let ρ := τ-1/2
  have hρ : unitAngleVector (ρ+1/2)=B.signedVector side := by
    simpa only [ρ,sub_add_cancel] using hτ
  refine ⟨ρ,hρ,?_⟩
  intro F hF
  have hbank := (Finset.mem_filter.mp hF).1
  have hFdef := (Finset.mem_filter.mp hbank).1
  have hFcode := (Finset.mem_filter.mp hbank).2
  have htwo := (Finset.mem_filter.mp hF).2.2.1
  change ((G.faceSourcePorts F).filter (fun e => ComponentCrosses cut (edgeComponent e))).card=2 at htwo
  obtain ⟨e,f,hne,hpair⟩ := Finset.card_eq_two.mp htwo
  have he : e∈(G.faceSourcePorts F).filter (fun e => ComponentCrosses cut (edgeComponent e)) := by
    rw [hpair]
    simp
  have hf : f∈(G.faceSourcePorts F).filter (fun e => ComponentCrosses cut (edgeComponent e)) := by
    rw [hpair]
    simp
  have hsharp (e : OrientedEdge G)
      (he : e∈(G.faceSourcePorts F).filter (fun e => ComponentCrosses cut (edgeComponent e))) :
      Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (sourceNormal e) := by
    have hp := Finset.mem_filter.mp he
    have hes := (Finset.mem_filter.mp hp.1).2
    have hh := B.crossing_signed_normal_cone ht e hes.1 (by rw [hes.2]; exact hFdef)
      ((componentGraph G ht).adj_symm hp.2)
    rw [hes.2,hFcode,← hρ] at hh
    exact hh
  exact ⟨e,(Finset.mem_filter.mp he).1,f,(Finset.mem_filter.mp hf).1,hne,hsharp e he,hsharp f hf⟩

theorem exists_isolated_bank_bin_boundaries (ht : G.TriangleFree)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a) (side : Bool) :
    ∃ ρ : ℝ,unitAngleVector (ρ+1/2)=B.signedVector side ∧
      ∀ F∈B.isolatedTwoPortPentagons ht side,
        ∃ P : PentagonFaceBoundary G F,Nonempty (P.BankBinData ρ) := by
  obtain ⟨ρ,hρ,hsharp⟩ := B.exists_isolated_two_sharp_bank_ports ht side
  refine ⟨ρ,hρ,?_⟩
  intro F hF
  have hFdef := (Finset.mem_filter.mp (Finset.mem_filter.mp hF).1).1
  exact G.l38_bank_bins_of_actual_ports ht hdegree F hFdef
    (Finset.mem_filter.mp hF).2.1 ρ (hsharp F hF)

end OrdinaryCutBanks

theorem PennyGraph.l38_isolated_subfamily_closed {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {W A : Finset (PlaneFace G)} (hW : G.IsJoinClosed ht W)
    (hAW : A⊆W)
    (hports : ∀ F∈A,∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents W) :
    G.IsJoinClosed ht A := by
  refine ⟨hAW.trans hW.subset_defects,?_⟩
  intro e f he hf hc heA hfdef
  have hs := G.boundary_face_singleton_joinClosed ht hW (G.sourceFace e) (hAW heA) (hports _ heA)
  have hface := hs.other_bounded_end e f he hf hc (Finset.mem_singleton_self _) hfdef
  simpa only [Finset.mem_singleton.mp hface] using heA

theorem PennyGraph.l38_boundary_port_transfer {n : ℕ} (G : PennyGraph n)
    {W V : Finset (PlaneFace G)} (e : OrientedEdge G) (he : SpineSource e)
    (heV : G.sourceFace e∈V) (hc : edgeComponent e∈G.familyBoundaryTrackComponents W) :
    edgeComponent e∈G.familyBoundaryTrackComponents V := by
  obtain ⟨f,hf,hfc⟩ := Finset.mem_image.mp hc
  have hfouter := (Finset.mem_filter.mp hf).2
  have hfsource := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2.1
  have heport : e∈G.familySourcePorts V := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heV⟩
  have hfcomp : edgeComponent f∈G.familyTrackComponents V :=
    hfc.symm ▸ Finset.mem_image.mpr ⟨e,heport,rfl⟩
  exact Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfsource,hfcomp⟩,hfouter⟩,hfc⟩

theorem TrackSystem.l38_crossings_empty_left (D : TrackSystem) (Z : Finset D.Track) :
    D.crossings ∅ Z=0 := by simp [crossings]

theorem TrackSystem.l38_crossings_empty_right (D : TrackSystem) (Z : Finset D.Track) :
    D.crossings Z ∅=0 := by simp [crossings]

theorem TrackSystem.l38_internal_empty (D : TrackSystem) : D.internal ∅=0 := by simp [internal]

theorem PennyGraph.l38_familyTrackIndices_empty {n : ℕ} (G : PennyGraph n) :
    G.familyTrackIndices ∅=∅ := by
  simp [PennyGraph.familyTrackIndices,PennyGraph.familyTrackComponents,PennyGraph.familySourcePorts]

theorem TrackSystem.l38_crossings_union_left (D : TrackSystem) (A B Z : Finset D.Track)
    (hAB : _root_.Disjoint A B) : D.crossings (A∪B) Z=D.crossings A Z+D.crossings B Z := by
  simp only [D.crossings_sum,Finset.sum_union hAB]

theorem TrackSystem.l38_crossings_union_right (D : TrackSystem) (Z A B : Finset D.Track)
    (hAB : _root_.Disjoint A B) : D.crossings Z (A∪B)=D.crossings Z A+D.crossings Z B := by
  simp only [D.crossings_sum,Finset.filter_union]
  have hcard (u : D.Track) :
      ((A.filter (D.crossing.Adj u))∪(B.filter (D.crossing.Adj u))).card=
        (A.filter (D.crossing.Adj u)).card+(B.filter (D.crossing.Adj u)).card :=
    Finset.card_union_of_disjoint (hAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  simp only [hcard,Finset.sum_add_distrib]

theorem PennyGraph.l38_crossings_union_left {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {A B : Finset (PlaneFace G)} (Z : Finset (PlaneFace G))
    (hA : G.IsJoinClosed ht A) (hB : G.IsJoinClosed ht B) (hAB : Disjoint A B) :
    G.interFamilyCrossings ht (A∪B) Z=G.interFamilyCrossings ht A Z+G.interFamilyCrossings ht B Z := by
  unfold PennyGraph.interFamilyCrossings
  rw [G.familyTrackIndices_union]
  exact TrackSystem.l38_crossings_union_left _ _ _ _ (G.familyTrackIndices_disjoint ht hA hB hAB)

theorem PennyGraph.l38_crossings_union_right {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Z : Finset (PlaneFace G)) {A B : Finset (PlaneFace G)}
    (hA : G.IsJoinClosed ht A) (hB : G.IsJoinClosed ht B) (hAB : Disjoint A B) :
    G.interFamilyCrossings ht Z (A∪B)=G.interFamilyCrossings ht Z A+G.interFamilyCrossings ht Z B := by
  unfold PennyGraph.interFamilyCrossings
  rw [G.familyTrackIndices_union]
  exact TrackSystem.l38_crossings_union_right _ _ _ _ (G.familyTrackIndices_disjoint ht hA hB hAB)

theorem PennyGraph.l38_crossings_sum_singletons_left {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (A Z : Finset (PlaneFace G))
    (hclosed : ∀ F∈A,G.IsJoinClosed ht {F}) :
    G.interFamilyCrossings ht A Z=∑ F∈A,G.interFamilyCrossings ht {F} Z := by
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    unfold PennyGraph.interFamilyCrossings
    rw [G.l38_familyTrackIndices_empty]
    exact TrackSystem.l38_crossings_empty_left _ _
  | @insert F A hFA ih =>
    have hAc : G.IsJoinClosed ht A := by
      refine ⟨?_,?_⟩
      · intro H hH
        exact (hclosed H (Finset.mem_insert_of_mem hH)).subset_defects (Finset.mem_singleton_self _)
      · intro e f he hf hc heA hfdef
        have h := (hclosed _ (Finset.mem_insert_of_mem heA)).other_bounded_end e f he hf hc
          (Finset.mem_singleton_self _) hfdef
        simpa only [Finset.mem_singleton.mp h] using heA
    rw [show insert F A={F}∪A by ext H; simp,
      G.l38_crossings_union_left ht Z (hclosed F (Finset.mem_insert_self _ _)) hAc (by simpa using hFA),
      ih (fun H hH => hclosed H (Finset.mem_insert_of_mem hH)),
      Finset.sum_union (by simpa using hFA : Disjoint ({F} : Finset (PlaneFace G)) A),Finset.sum_singleton]

theorem PennyGraph.l38_crossings_sum_singletons_right {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Z A : Finset (PlaneFace G))
    (hclosed : ∀ F∈A,G.IsJoinClosed ht {F}) :
    G.interFamilyCrossings ht Z A=∑ F∈A,G.interFamilyCrossings ht Z {F} := by
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    unfold PennyGraph.interFamilyCrossings
    rw [G.l38_familyTrackIndices_empty]
    exact TrackSystem.l38_crossings_empty_right _ _
  | @insert F A hFA ih =>
    have hAc : G.IsJoinClosed ht A := by
      refine ⟨?_,?_⟩
      · intro H hH
        exact (hclosed H (Finset.mem_insert_of_mem hH)).subset_defects (Finset.mem_singleton_self _)
      · intro e f he hf hc heA hfdef
        have h := (hclosed _ (Finset.mem_insert_of_mem heA)).other_bounded_end e f he hf hc
          (Finset.mem_singleton_self _) hfdef
        simpa only [Finset.mem_singleton.mp h] using heA
    rw [show insert F A={F}∪A by ext H; simp,
      G.l38_crossings_union_right ht Z (hclosed F (Finset.mem_insert_self _ _)) hAc (by simpa using hFA),
      ih (fun H hH => hclosed H (Finset.mem_insert_of_mem hH)),
      Finset.sum_union (by simpa using hFA : Disjoint ({F} : Finset (PlaneFace G)) A),Finset.sum_singleton]

theorem PennyGraph.l38_isolated_pentagons_internal_bound {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    {W A : Finset (PlaneFace G)} (hW : G.IsJoinClosed ht W) (hAW : A⊆W)
    (hfive : ∀ F∈A,(G.faceSourcePorts F).card=5)
    (hports : ∀ F∈A,∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents W)
    (ρ : ℝ) (hbank : ∀ F∈A,G.l38TwoSharpBankPorts ρ F) :
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
    have hrec := ih hAW' (fun H hH => hfive H (hsub hH)) hpA (fun H hH => hbank H (hsub hH))
    have hcross : G.interFamilyCrossings ht {F} A≤3*A.card := by
      rw [G.l38_crossings_sum_singletons_right ht {F} A hsingle]
      calc
        _ ≤ ∑ _∈A,3 := Finset.sum_le_sum (fun H hH => by
          obtain ⟨P,⟨D⟩⟩ := G.l38_bank_bins_of_actual_ports ht hdegree F (hW.subset_defects hFW)
            (hfive F (Finset.mem_insert_self _ _)) ρ (hbank F (Finset.mem_insert_self _ _))
          obtain ⟨Q,⟨E⟩⟩ := G.l38_bank_bins_of_actual_ports ht hdegree H (hW.subset_defects (hAW' hH))
            (hfive H (hsub hH)) ρ (hbank H (hsub hH))
          exact G.isolated_pentagon_pair_crossings_le_three_of_bins ht hW P Q hFW (hAW' hH)
            (by intro h; exact hFA (h ▸ hH)) hpF (hpA H hH) D E)
        _ = 3*A.card := by simp [Nat.mul_comm]
    have hsplit := G.family_internal_crossings_union ht hFc hAc (by simpa using hFA)
    have hzero := G.five_port_internal_crossings_zero ht F (hW.subset_defects hFW) hdegree
      (hfive F (Finset.mem_insert_self _ _))
    rw [show {F}∪A=insert F A by ext H; simp,hzero,zero_add] at hsplit
    rw [hsplit,Finset.card_insert_of_notMem hFA]
    have hcross' : (G.interFamilyCrossings ht {F} A : ℤ)≤3*(A.card : ℤ) := by exact_mod_cast hcross
    push_cast
    nlinarith only [hrec,hcross']

theorem PennyGraph.l38_isolated_pentagons_X_bound {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    {W A : Finset (PlaneFace G)} (hW : G.IsJoinClosed ht W) (hAW : A⊆W)
    (hfive : ∀ F∈A,(G.faceSourcePorts F).card=5)
    (hports : ∀ F∈A,∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents W)
    (ρ : ℝ) (hbank : ∀ F∈A,G.l38TwoSharpBankPorts ρ F) :
    (G.familyInternalCrossings ht A : ℝ)+A.card≤3*(A.card : ℝ)^2/2 := by
  have h := G.l38_isolated_pentagons_internal_bound ht hdegree hW hAW hfive hports ρ hbank
  have hr : 2*(G.familyInternalCrossings ht A : ℝ)≤3*(A.card : ℝ)*(A.card-1) := by exact_mod_cast h
  nlinarith only [hr,show (0:ℝ)≤A.card by positivity]

theorem PennyGraph.l38_isolated_pentagons_M_bound {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    {W A Z : Finset (PlaneFace G)} (hW : G.IsJoinClosed ht W) (hAW : A⊆W)
    (hZ : G.IsJoinClosed ht Z) (hAZ : Disjoint A Z)
    (hfive : ∀ F∈A,(G.faceSourcePorts F).card=5)
    (hports : ∀ F∈A,∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents W) :
    (G.interFamilyCrossings ht A Z : ℤ)≤(A.card : ℤ)*(G.familyK Z+G.familyPortExcess Z) := by
  have hsingle (F) (hF : F∈A) := G.boundary_face_singleton_joinClosed ht hW F (hAW hF) (hports F hF)
  have hpoint (F) (hF : F∈A) :
      (G.interFamilyCrossings ht {F} Z : ℤ)≤ G.familyK Z+G.familyPortExcess Z := by
    have hFZ : F∉Z := fun h => Finset.disjoint_left.mp hAZ hF h
    have hrest : ({F}∪Z)\{F}=Z := by
      ext H
      by_cases h : H=F
      · subst H
        simp [hFZ]
      · simp [h]
    have hp (e) (he : e∈G.faceSourcePorts F) :
        edgeComponent e∈G.familyBoundaryTrackComponents ({F}∪Z) := by
      have hes := (Finset.mem_filter.mp he).2
      apply G.l38_boundary_port_transfer e hes.1
      · rw [hes.2]; exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      · exact hports F hF e he
    have hm := G.pentagon_crossing_estimate ht hdegree ({F}∪Z) ((hsingle F hF).union hZ)
      F (Finset.mem_union_left _ (Finset.mem_singleton_self _)) (hfive F hF) hp
    rw [hrest] at hm
    have htrack := G.family_tracks_boundary_add_joins ht hZ
    have hport := G.family_ports_boundary_add_twice_joins ht hZ
    rw [← G.familySourcePorts_card] at hport
    have hex : G.familyPortExcess Z=(G.familySourcePorts Z).card-4*Z.card := by
      rw [G.familyPortExcess_eq,G.familySourcePorts_card,Nat.cast_sum]
    unfold PennyGraph.familyK
    omega
  rw [G.l38_crossings_sum_singletons_left ht A Z hsingle,Nat.cast_sum]
  calc
    _ ≤ ∑ _∈A,(G.familyK Z+G.familyPortExcess Z) := Finset.sum_le_sum (fun F hF => hpoint F hF)
    _ = _ := by simp [mul_comm]

end Swanepoel
