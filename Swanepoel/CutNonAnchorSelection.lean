module
public import Swanepoel.CutHalfAccounting
public import Swanepoel.DisjointReduction
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem canonicalInheritedNonAnchors_disjoint (ht : G.TriangleFree) (side : Bool) :
    (B.canonicalHalfTracks ht side).Disjoint (B.canonicalInheritedNonAnchors ht side) := by
  intro u hu v hv huv
  have huc := (Finset.mem_filter.mp hu).2.1
  have hvc := (Finset.mem_filter.mp hv).2.1
  have huv' : ComponentCrosses (B.canonicalHalfComponent ht side u)
      (B.canonicalHalfComponent ht side v) :=
    (B.halfComponentMap_crossing_iff ht side _ _).mp huv
  exact componentGraph_noTriple G ht cut _ _ huc huv'
    ((componentGraph G ht).adj_symm hvc)

theorem canonicalInheritedNonAnchors_subset_ordinary (ht : G.TriangleFree) (side : Bool) :
    B.canonicalInheritedNonAnchors ht side⊆(B.canonicalHalfTracks ht side).ordinary := by
  intro u hu
  exact (Finset.mem_filter.mp hu).1

theorem canonicalInheritedNonAnchors_subset_disjoint (ht : G.TriangleFree) (side : Bool)
    (A : Finset (B.canonicalHalfTracks ht side).Track)
    (hA : A⊆B.canonicalInheritedNonAnchors ht side) :
    (B.canonicalHalfTracks ht side).Disjoint A := by
  intro u hu v hv
  exact B.canonicalInheritedNonAnchors_disjoint ht side u (hA hu) v (hA hv)

theorem canonicalInheritedNonAnchors_exists_subset (ht : G.TriangleFree) (side : Bool)
    (a : ℕ) (ha : a≤(B.canonicalInheritedNonAnchors ht side).card) :
    ∃ A : Finset (B.canonicalHalfTracks ht side).Track,
      A⊆B.canonicalInheritedNonAnchors ht side ∧ A.card=a ∧
      A⊆(B.canonicalHalfTracks ht side).ordinary ∧
      (B.canonicalHalfTracks ht side).Disjoint A := by
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq ha
  exact ⟨A,hA,hcard,hA.trans (B.canonicalInheritedNonAnchors_subset_ordinary ht side),
    B.canonicalInheritedNonAnchors_subset_disjoint ht side A hA⟩

theorem canonical_small_bank_selection_size (ht : G.TriangleFree)
    (hc : G.graph.Connected) (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (hhigh : 61*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K<
      100*(B.terminalCutCrossers.card : ℤ))
    (hsmall : 100*(B.canonicalHalfSystem ht side).d<39*(B.canonicalHalfSystem ht side).k) :
    0≤(B.canonicalHalfSystem ht side).k-2*(B.canonicalHalfSystem ht side).d ∧
      ((B.canonicalHalfSystem ht side).k-2*(B.canonicalHalfSystem ht side).d).toNat≤
        (B.canonicalInheritedNonAnchors ht side).card := by
  let D := componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)
  let H := B.canonicalHalfSystem ht side
  let J := B.canonicalHalfSystem ht (!side)
  let z : ℤ := (B.splitTerminalJoins ht).card
  let s : ℤ := B.terminalCutCrossers.card
  let o : ℤ := (B.canonicalInheritedNonAnchors ht side).card
  change 61*D.K<100*s at hhigh
  change 100*H.d<39*H.k at hsmall
  have hcons := B.canonical_cut_conservation ht hc hcut
  have hk : H.k+J.k=D.K+z := by
    cases side
    · exact hcons.1
    · exact (add_comm _ _).trans hcons.1
  have hd : H.d+J.d=s+z := by
    cases side
    · exact hcons.2.1
    · exact (add_comm _ _).trans hcons.2.1
  have ho : H.d+o=s := hcons.2.2 side
  have hz : 0≤z := Nat.cast_nonneg _
  have hzH : z≤H.d := by
    change ((B.splitTerminalJoins ht).card : ℤ)≤(B.canonicalHalfSystem ht side).d
    rw [(B.canonicalHalfBankRealization ht hc hcut side).d_eq_bankMeetingAnchors]
    exact_mod_cast B.split_join_count_le_meeting ht hcut side
  have hJ : 10*J.d≤9*J.k :=
    (B.canonicalHalfBankRealization ht hc hcut (!side)).bankBound
  have hsize : H.k-2*H.d≤o := cut_enough_nonanchors D.K s z H.k J.k H.d J.d o
    (G.canonical_componentSystem_K_nonneg ht) hz hzH hhigh hk hd ho hsmall hJ
  have hd0 : 0≤H.d := by
    change 0≤(H.bankAnchors.card : ℤ)
    exact Nat.cast_nonneg _
  have ha0 : 0≤H.k-2*H.d := by omega
  change 0≤H.k-2*H.d ∧ (H.k-2*H.d).toNat≤(B.canonicalInheritedNonAnchors ht side).card
  refine ⟨ha0,?_⟩
  dsimp only [o] at hsize
  omega

theorem canonical_small_bank_selection (ht : G.TriangleFree)
    (hc : G.graph.Connected) (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (hhigh : 61*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K<
      100*(B.terminalCutCrossers.card : ℤ))
    (hsmall : 100*(B.canonicalHalfSystem ht side).d<39*(B.canonicalHalfSystem ht side).k) :
    ∃ A : Finset (B.canonicalHalfTracks ht side).Track,
      A⊆B.canonicalInheritedNonAnchors ht side ∧
      A.card=((B.canonicalHalfSystem ht side).k-2*(B.canonicalHalfSystem ht side).d).toNat ∧
      (A.card : ℤ)=(B.canonicalHalfSystem ht side).k-2*(B.canonicalHalfSystem ht side).d ∧
      A⊆(B.canonicalHalfTracks ht side).ordinary ∧
      (B.canonicalHalfTracks ht side).Disjoint A := by
  obtain ⟨ha0,hsize⟩ := B.canonical_small_bank_selection_size ht hc hcut side hhigh hsmall
  obtain ⟨A,hA,hcard,hord,hdisj⟩ := B.canonicalInheritedNonAnchors_exists_subset ht side _ hsize
  refine ⟨A,hA,hcard,?_,hord,hdisj⟩
  rw [hcard,Int.toNat_of_nonneg ha0]

theorem canonicalInheritedNonAnchors_sum_partition (ht : G.TriangleFree) (side : Bool)
    (A : Finset (B.canonicalHalfTracks ht side).Track)
    (hA : A⊆B.canonicalInheritedNonAnchors ht side) :
    (∑ u∈B.canonicalInheritedNonAnchors ht side,((B.canonicalHalfTracks ht side).s u : ℤ))=
      (∑ u∈A,((B.canonicalHalfTracks ht side).s u : ℤ))+
        ∑ u∈B.canonicalInheritedNonAnchors ht side\A,
          ((B.canonicalHalfTracks ht side).s u : ℤ) := by
  have h := Finset.sum_sdiff (f := fun u => ((B.canonicalHalfTracks ht side).s u : ℤ)) hA
  omega

theorem canonicalInheritedNonAnchors_remainder_sum_le (ht : G.TriangleFree)
    (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (A : Finset (B.canonicalHalfTracks ht side).Track)
    (hA : A⊆B.canonicalInheritedNonAnchors ht side) :
    (∑ u∈B.canonicalInheritedNonAnchors ht side\A,
      ((B.canonicalHalfTracks ht side).s u : ℤ))≤
        ((B.canonicalInheritedNonAnchors ht side).card-(A.card : ℤ))*
          ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := by
  have hb := (B.canonicalHalfBankRealization ht hc hcut side).nonAnchorBound hdegree hcut
  have hcard : ((B.canonicalInheritedNonAnchors ht side\A).card : ℤ)=
      (B.canonicalInheritedNonAnchors ht side).card-(A.card : ℤ) := by
    have h := Finset.card_sdiff_add_card_eq_card hA
    omega
  calc
    _≤∑ _u∈B.canonicalInheritedNonAnchors ht side\A,
        ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hb u (B.canonicalInheritedNonAnchors_subset ht side (Finset.mem_sdiff.mp hu).1)
    _=_ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [hcard]

theorem canonical_small_bank_sum_cap (ht : G.TriangleFree)
    (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (hhigh : 61*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K<
      100*(B.terminalCutCrossers.card : ℤ))
    (hsmall : 100*(B.canonicalHalfSystem ht side).d<39*(B.canonicalHalfSystem ht side).k)
    (hrec : (B.canonicalHalfTracks ht side).DisjointBound) :
    (B.canonicalHalfSystem ht side).R+
      (∑ u∈B.canonicalInheritedNonAnchors ht side,((B.canonicalHalfTracks ht side).s u : ℤ))≤
        ((B.canonicalHalfSystem ht side).d+(B.canonicalInheritedNonAnchors ht side).card)*
          ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := by
  obtain ⟨A,hA,_hcard,hcardZ,hord,hdisj⟩ :=
    B.canonical_small_bank_selection ht hc hcut side hhigh hsmall
  have hchosen : (B.canonicalHalfSystem ht side).R+
      (∑ u∈A,((B.canonicalHalfTracks ht side).s u : ℤ))≤
        N ((B.canonicalHalfSystem ht side).k+A.card) := hrec A hord hdisj
  have hothers := B.canonicalInheritedNonAnchors_remainder_sum_le ht hc hdegree hcut side A hA
  have hcap := cut_recursive_cap (B.canonicalHalfSystem ht side).k
    (B.canonicalHalfSystem ht side).d
    ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d)
    (B.canonicalInheritedNonAnchors ht side).card A.card
    (B.canonicalHalfSystem ht side).R
    (∑ u∈A,((B.canonicalHalfTracks ht side).s u : ℤ))
    (∑ u∈B.canonicalInheritedNonAnchors ht side\A,((B.canonicalHalfTracks ht side).s u : ℤ))
    rfl hcardZ hchosen hothers
  rw [B.canonicalInheritedNonAnchors_sum_partition ht side A hA]
  simpa only [add_assoc] using hcap

theorem canonical_small_bank_cap (ht : G.TriangleFree)
    (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (hhigh : 61*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K<
      100*(B.terminalCutCrossers.card : ℤ))
    (hsmall : 100*(B.canonicalHalfSystem ht side).d<39*(B.canonicalHalfSystem ht side).k)
    (hrec : (B.canonicalHalfTracks ht side).DisjointBound) :
    (B.canonicalHalfSystem ht side).R+(B.inheritedNonAnchorCrossings ht side : ℤ)≤
      ((B.canonicalHalfSystem ht side).d+(B.inheritedNonAnchors ht side).card)*
        ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := by
  have hcap := B.canonical_small_bank_sum_cap ht hc hdegree hcut side hhigh hsmall hrec
  rw [B.inheritedNonAnchorCrossings_eq_sum ht hc hcut side,Nat.cast_sum,
    ← B.canonicalInheritedNonAnchors_card ht hc hcut side]
  exact hcap

end OrdinaryCutBanks
end Swanepoel
