module
public import Swanepoel.L38BankRestrictionThree
public import Swanepoel.HalfSystemBankRealization
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem remainderK_nonneg (ht : G.TriangleFree) (side : Bool) :
    0≤G.familyK (B.bankRemainder ht side) := by
  have h := G.partial_family_three_boundary_le_five_K ht (B.bankRemainder ht side)
    ((B.bankRemainder_subset ht side).trans (Finset.filter_subset _ _))
  have hB : (0:ℤ)≤(G.familyUnpairedPorts (B.bankRemainder ht side)).card := Nat.cast_nonneg _
  omega

theorem remainderPortExcess_nonneg (ht : G.TriangleFree) (side : Bool) :
    0≤G.familyPortExcess (B.bankRemainder ht side) := by
  unfold PennyGraph.familyPortExcess
  apply Finset.sum_nonneg
  intro F hF
  have hm := G.defect_source_ports_five_le ht F
    (Finset.mem_filter.mp (B.bankRemainder_subset ht side hF)).1
  have hmZ : (5:ℤ)≤(G.faceSourcePorts F).card := by exact_mod_cast hm
  omega

theorem bank_arithmetic_parameters (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a) :
    let S := B.isolatedTwoPortPentagons ht side
    let Y := B.bankRemainder ht side
    let ell : ℝ := S.card
    let k : ℝ := G.familyK Y
    let y : ℝ := (B.subfamilyMeetingPorts Y).card
    let h : ℝ := G.familyPortExcess Y
    0≤ell ∧ 0≤k ∧ 0≤y ∧ 0≤h ∧
      (B.bankK ht side : ℝ)=3*ell+k ∧
      ((B.bankMeetingAnchors ht side).card : ℝ)=2*ell+y ∧
      y≤4*h-k ∧ 2*y≤h+k ∧ 9*y≤10*k-5*h := by
  have hid := B.bank_partition_counts ht side
  have hK : B.bankK ht side=
      3*(B.isolatedTwoPortPentagons ht side).card+G.familyK (B.bankRemainder ht side) := by
    simpa only [bankK,bankAnchorTracks,PennyGraph.familyK] using hid.2.1
  have hD : (B.bankMeetingAnchors ht side).card=
      2*(B.isolatedTwoPortPentagons ht side).card+
        (B.subfamilyMeetingPorts (B.bankRemainder ht side)).card := by
    have hd := hid.1
    change (B.bankMeetingPorts ht side).card=_ at hd
    rwa [B.bankMeetingPorts_card ht side] at hd
  dsimp only
  refine ⟨Nat.cast_nonneg _,?_,Nat.cast_nonneg _,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast B.remainderK_nonneg ht side
  · exact_mod_cast B.remainderPortExcess_nonneg ht side
  · exact_mod_cast hK
  · exact_mod_cast hD
  · exact_mod_cast B.remainder_restriction_three ht side hdegree
  · exact_mod_cast B.subfamily_restriction_four ht side hdegree (B.bankRemainder ht side)
      (B.bankRemainder_subset ht side)
  · exact_mod_cast B.subfamily_restriction_five ht side (B.bankRemainder ht side)
      (B.bankRemainder_subset ht side)

end OrdinaryCutBanks

theorem HalfSystem.BankRealization.k_eq_bankK {n : ℕ} {G : PennyGraph n}
    {cut : TrackComponent G} {H : HalfSystem} {B : OrdinaryCutBanks G cut}
    {ht : G.TriangleFree} {side : Bool} (R : H.BankRealization B ht side) :
    H.k=B.bankK ht side := by
  have hp : H.tracks.p=(B.bankAnchorTracks ht side).card := by
    rw [← R.anchors,Finset.card_image_of_injective _ R.injective]
    rfl
  change H.tracks.K=B.bankK ht side
  rw [TrackSystem.K,hp,R.defects]
  rfl

theorem HalfSystem.BankRealization.d_eq_bankMeetingAnchors {n : ℕ} {G : PennyGraph n}
    {cut : TrackComponent G} {H : HalfSystem} {B : OrdinaryCutBanks G cut}
    {ht : G.TriangleFree} {side : Bool} (R : H.BankRealization B ht side) :
    H.d=((B.bankMeetingAnchors ht side).card : ℤ) := by
  have hd : H.bankAnchors.card=(B.bankMeetingAnchors ht side).card := by
    rw [← R.bank,Finset.card_image_of_injective _ R.injective]
  change (H.bankAnchors.card : ℤ)=_
  exact_mod_cast hd

theorem HalfSystem.BankRealization.bank_arithmetic_parameters {n : ℕ} {G : PennyGraph n}
    {cut : TrackComponent G} {H : HalfSystem} {B : OrdinaryCutBanks G cut}
    {ht : G.TriangleFree} {side : Bool} (R : H.BankRealization B ht side)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a) :
    let S := B.isolatedTwoPortPentagons ht side
    let Y := B.bankRemainder ht side
    let ell : ℝ := S.card
    let k : ℝ := G.familyK Y
    let y : ℝ := (B.subfamilyMeetingPorts Y).card
    let h : ℝ := G.familyPortExcess Y
    0≤ell ∧ 0≤k ∧ 0≤y ∧ 0≤h ∧
      (H.k : ℝ)=3*ell+k ∧ (H.d : ℝ)=2*ell+y ∧
      y≤4*h-k ∧ 2*y≤h+k ∧ 9*y≤10*k-5*h := by
  simpa only [R.k_eq_bankK,R.d_eq_bankMeetingAnchors,Int.cast_natCast] using
    B.bank_arithmetic_parameters ht side hdegree

end Swanepoel
