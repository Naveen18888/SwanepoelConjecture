module
public import Swanepoel.JoinClosedPentagons
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.familyR {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) : ℤ := (G.familyInternalCrossings ht Y : ℤ)+Y.card

structure FivePortRemovalCounts {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) (F : PlaneFace G) : Prop where
  singleton_closed : G.IsJoinClosed ht {F}
  remainder_closed : G.IsJoinClosed ht (Y\{F})
  K : G.familyK Y=3+G.familyK (Y\{F})
  boundary : G.familyBoundaryEndCount Y=5+G.familyBoundaryEndCount (Y\{F})
  defects : (Y\{F}).card+1=Y.card
  crossings : G.familyInternalCrossings ht Y=G.familyInternalCrossings ht {F}+
    G.familyInternalCrossings ht (Y\{F})+G.interFamilyCrossings ht {F} (Y\{F})

theorem PennyGraph.five_port_removal_counts {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y) (hfive : (G.faceSourcePorts F).card=5)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y) :
    FivePortRemovalCounts G ht Y F := by
  have hF := G.boundary_face_singleton_joinClosed ht hY F hFY hports
  have hrest := hY.sdiff hF
  have hKF := G.boundary_five_port_singleton_K ht hY F hFY hfive hports
  have hsub : ({F} : Finset (PlaneFace G))⊆Y := Finset.singleton_subset_iff.mpr hFY
  have hU : {F}∪(Y\{F})=Y := Finset.union_sdiff_of_subset hsub
  have hdis : Disjoint ({F} : Finset (PlaneFace G)) (Y\{F}) := Finset.disjoint_left.mpr (by
    intro H hHF hHR
    exact (Finset.mem_sdiff.mp hHR).2 hHF)
  have hK := G.familyK_union ht hF hrest hdis
  rw [hU,hKF] at hK
  have hBF : G.familyBoundaryEndCount {F}=5 := by
    have hbalance := G.family_K_port_conservation ht hF
    have hexcess : G.familyPortExcess {F}=1 := by simp [PennyGraph.familyPortExcess,hfive]
    rw [hKF,hexcess] at hbalance
    omega
  have hB := G.familyBoundaryEndCount_union ht hF hrest hdis
  rw [hU,hBF] at hB
  have hcross := G.family_internal_crossings_union ht hF hrest hdis
  rw [hU] at hcross
  exact ⟨hF,hrest,hK,hB,by
    simpa only [Finset.card_singleton] using Finset.card_sdiff_add_card_eq_card hsub,hcross⟩

def PennyGraph.PentagonCrossingEstimate {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : Prop :=
  ∀ (Y : Finset (PlaneFace G)), G.IsJoinClosed ht Y → ∀ F∈Y,
    (G.faceSourcePorts F).card=5 →
    (∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y) →
    (G.interFamilyCrossings ht {F} (Y\{F}) : ℤ)+G.familyJoinCount (Y\{F})≤
      2*((G.familySourcePorts (Y\{F})).card : ℤ)-6*(Y\{F}).card

theorem FivePortRemovalCounts.loss_bound {n : ℕ} {G : PennyGraph n} {ht : G.TriangleFree}
    {Y : Finset (PlaneFace G)} {F : PlaneFace G} (C : FivePortRemovalCounts G ht Y F)
    (hdisjoint : G.familyInternalCrossings ht {F}=0)
    (hmixed : (G.interFamilyCrossings ht {F} (Y\{F}) : ℤ)+G.familyJoinCount (Y\{F})≤
      2*((G.familySourcePorts (Y\{F})).card : ℤ)-6*(Y\{F}).card) :
    G.familyR ht Y≤G.familyR ht (Y\{F})+3*G.familyK Y-G.familyBoundaryEndCount Y-3 := by
  have htracks := G.family_tracks_boundary_add_joins ht C.remainder_closed
  have hports : (G.familySourcePorts (Y\{F})).card=
      G.familyBoundaryEndCount (Y\{F})+2*G.familyJoinCount (Y\{F}) := by
    rw [G.familySourcePorts_card,G.family_ports_boundary_add_twice_joins ht C.remainder_closed]
  have hcross := C.crossings
  rw [hdisjoint,zero_add] at hcross
  have hK := C.K
  have hB := C.boundary
  have hf := C.defects
  have hKrest : G.familyK (Y\{F})=(G.familyTrackComponents (Y\{F})).card-2*(Y\{F}).card := rfl
  unfold PennyGraph.familyR
  omega

theorem pentagon_quadratic_step (K B R R' : ℤ) (hK : 0≤K) (hlarge : 8*K<5*B)
    (hloss : R≤R'+3*K-B-3) (hrec : 10000*R'≤2379*(K-3)^2) :
    10000*R≤2379*K^2 := by
  nlinarith

end Swanepoel
