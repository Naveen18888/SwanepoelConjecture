module
public import Swanepoel.L38PentagonNormalGeometry
public import Swanepoel.L38PentagonBinCapacity
public import Swanepoel.CornerAngleGeometry
@[expose] public section

noncomputable section
namespace Swanepoel

theorem l38_bank_normal_phase (ρ : ℝ) (normal : Plane) (hn : ‖normal‖=1)
    (hbank : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) normal) :
    ∃ a : ℝ,0< a ∧ a<1 ∧ unitAngleVector (ρ+a)=normal := by
  obtain ⟨a,ha,hphase⟩ := exists_relative_unitAngleVector normal hn ρ 0
  have hcone : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+(-1)+3/2)) (unitAngleVector (ρ+a)) := by
    rw [show ρ+(-1)+3/2=ρ+1/2 by ring,hphase]
    exact hbank
  have hh := positive_sharp_phase_interval ρ (-1) a (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2]) hcone
  exact ⟨a,by linarith [hh.1],by linarith [hh.2],hphase⟩

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem normal_injective (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) : Function.Injective P.normal := by
  intro i j hij
  by_contra hne
  have hfinite : ∀ i j : Fin 5,i≠j → j=i+1 ∨ j=i+2 ∨ i=j+1 ∨ i=j+2 := by decide
  rcases hfinite i j hne with h | h | h | h
  · have hc := P.normal_clockwise_turn ht hF i
    rw [← h,← hij,cross2_self] at hc
    exact lt_irrefl _ hc
  · have hc := P.normal_two_step_inner_le ht hF i
    rw [← h,← hij,real_inner_self_eq_norm_sq,P.normal_norm] at hc
    norm_num at hc
  · have hc := P.normal_clockwise_turn ht hF j
    rw [← h,hij,cross2_self] at hc
    exact lt_irrefl _ hc
  · have hc := P.normal_two_step_inner_le ht hF j
    rw [← h,hij,real_inner_self_eq_norm_sq,P.normal_norm] at hc
    norm_num at hc

theorem bank_phase_pair_predecessor (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (ρ a b : ℝ) (ha : 0< a) (hab : a< b) (hb : b<1)
    (i j : Fin 5) (h0 : unitAngleVector (ρ+a)=P.normal i)
    (h4 : unitAngleVector (ρ+b)=P.normal j) : j=i+4 := by
  have hp : 0< Real.pi/3 := by positivity
  have hc : 0< cross2 (P.normal i) (P.normal j) := by
    rw [← h0,← h4,unitAngleVector_cross,show (ρ+b)-(ρ+a)=b-a by ring]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith only [hp,ha,hb])
  have hne : i≠j := by intro h; rw [h,cross2_self] at hc; exact lt_irrefl _ hc
  have hfinite : ∀ i j : Fin 5,i≠j → j=i+1 ∨ j=i+2 ∨ i=j+1 ∨ i=j+2 := by decide
  rcases hfinite i j hne with h | h | h | h
  · have hn := P.normal_clockwise_turn ht hF i
    rw [← h] at hn
    linarith only [hc,hn]
  · have hn := P.normal_two_step_inner_le ht hF i
    rw [← h,← h0,← h4] at hn
    have hpos := unitAngleVector_inner_pos_of_gap (ρ+a) (ρ+b) (by constructor <;> linarith only [ha,hab,hb])
    linarith only [hn,hpos]
  · calc
      j=(j+1)+4 := by fin_cases j <;> decide
      _=i+4 := by rw [← h]
  · have hn := P.normal_two_step_inner_le ht hF j
    rw [← h,real_inner_comm,← h0,← h4] at hn
    have hpos := unitAngleVector_inner_pos_of_gap (ρ+a) (ρ+b) (by constructor <;> linarith only [ha,hab,hb])
    linarith only [hn,hpos]

def bankShift (k : Fin 5) : PentagonFaceBoundary G F where
  vertex i := P.vertex (k+i)
  vertex_injective := P.vertex_injective.comp (Equiv.addLeft k).injective
  contact i := by simpa only [add_assoc] using P.contact (k+i)
  face i := by simpa only [add_assoc] using P.face (k+i)
  darts := by
    rw [← P.darts]
    ext e
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨k+i,?_⟩
      apply Subtype.ext
      simp only [add_assoc]
    · rintro ⟨j,rfl⟩
      obtain ⟨i,rfl⟩ := (Equiv.addLeft k).surjective j
      refine ⟨i,?_⟩
      apply Subtype.ext
      change (P.vertex (k+i),P.vertex (k+(i+1)))=
        (P.vertex (k+i),P.vertex ((k+i)+1))
      simp only [add_assoc]

theorem bankShift_normal (k i : Fin 5) : (P.bankShift k).normal i=P.normal (k+i) := by
  simp [normal,dart,bankShift,add_assoc]

theorem bank_bin_data_of_bank_pair (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (ρ a b : ℝ) (ha : 0< a) (hab : a< b) (hb : b<1)
    (h0 : unitAngleVector (ρ+a)=P.normal 0)
    (h4 : unitAngleVector (ρ+b)=P.normal 4) : Nonempty (P.BankBinData ρ) := by
  have hb0 : 0< b := lt_trans ha hab
  have ha1 : a<1 := lt_trans hab hb
  have hg : 0< b-a := sub_pos.mpr hab
  have hc34 := P.normal_clockwise_turn ht hF 3
  have hd34 := P.normal_adjacent_inner_gt_neg_half ht 3
  norm_num at hc34 hd34
  obtain ⟨A,hA0,hA2,hA⟩ := counterclockwise_unitAngle_gap (ρ+b) (P.normal 3) (P.normal_norm 3)
    (by rw [h4]; have hs : cross2 (P.normal 4) (P.normal 3)= -cross2 (P.normal 3) (P.normal 4) := by unfold cross2; ring
        rw [hs]; linarith only [hc34])
    (by rw [h4,real_inner_comm]; linarith only [hd34])
  have hAg : 2≤ A+(b-a) := by
    have hd := P.normal_two_step_inner_le ht hF 3
    norm_num at hd
    rw [← hA,← h0,unitAngleVector_inner,
      show Real.pi/3*((ρ+a)-((ρ+b)+A))= -(Real.pi/3*(A+(b-a))) by ring,Real.cos_neg] at hd
    exact two_le_of_cos_le_neg_half _ (by linarith only [hA0,hg]) (by linarith only [hd])
  have h3lo : 2< b+A := by linarith only [hAg,ha]
  have h3hi : b+A<3 := by linarith only [hA2,hb]
  obtain ⟨B,hB0,hB2,hB⟩ := clockwise_unitAngle_gap (ρ+a) (P.normal 1) (P.normal_norm 1)
    (by rw [h0]; exact P.normal_clockwise_turn ht hF 0)
    (by rw [h0]; exact P.normal_adjacent_inner_gt_neg_half ht 0)
  have hBg : 2≤ B+(b-a) := by
    have hd := P.normal_two_step_inner_le ht hF 4
    norm_num at hd
    rw [← h4,← hB,unitAngleVector_inner,
      show Real.pi/3*(((ρ+a)-B)-(ρ+b))= -(Real.pi/3*(B+(b-a))) by ring,Real.cos_neg] at hd
    exact two_le_of_cos_le_neg_half _ (by linarith only [hB0,hg]) (by linarith only [hd])
  have h1lo : 4< a-B+6 := by linarith only [hB2,ha]
  have h1hi : a-B+6<5 := by linarith only [hBg,hb]
  have hphase1 : unitAngleVector (ρ+(a-B+6))=P.normal 1 := by
    rw [show ρ+(a-B+6)=((ρ+a)-B)+6 by ring,unitAngleVector_periodic,hB]
  have hc02 := P.normal_two_step_clockwise ht hF 0
  have hd02 := P.normal_two_step_inner_le ht hF 0
  norm_num at hc02 hd02
  obtain ⟨C,hC0,hC2,hC⟩ := counterclockwise_unitAngle_gap (ρ+a) (-P.normal 2)
    (by simpa using P.normal_norm 2)
    (by rw [h0]; have hs : cross2 (P.normal 0) (-P.normal 2)= -cross2 (P.normal 0) (P.normal 2) := by unfold cross2; simp; ring
        rw [hs]; linarith only [hc02])
    (by rw [h0,inner_neg_right]; linarith only [hd02])
  have hC1 : C≤1 := by
    have hi : (1/2:ℝ)≤ inner ℝ (P.normal 0) (-P.normal 2) := by rw [inner_neg_right]; linarith only [hd02]
    rw [← h0,← hC,unitAngleVector_inner,add_sub_cancel_left] at hi
    by_contra hn
    have hp : 0< Real.pi/3 := by positivity
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show 0≤ Real.pi/3 by positivity)
      (show Real.pi/3*C≤ Real.pi by nlinarith only [hp,hC2])
      (show Real.pi/3< Real.pi/3*C by nlinarith only [hp,lt_of_not_ge hn])
    rw [Real.cos_pi_div_three] at hh
    linarith only [hi,hh]
  have hphase2 : unitAngleVector (ρ+(a+C+3))=P.normal 2 := by
    rw [show ρ+(a+C+3)=((ρ+a)+C)+3 by ring,unitAngleVector_add_three,hC,neg_neg]
  have h2lo : 3< a+C+3 := by linarith only [ha,hC0]
  have h2hi : a+C+3<4 := by
    have hc24 := P.normal_two_step_clockwise ht hF 2
    norm_num at hc24
    rw [← hphase2,← h4,unitAngleVector_cross,
      show Real.pi/3*((ρ+b)-(ρ+(a+C+3)))= -(Real.pi/3*((a+C+3)-b)) by ring,Real.sin_neg] at hc24
    have hgap : a+C+3-b<3 := by
      by_contra hn
      have hp : 0< Real.pi/3 := by positivity
      have hs := Real.sin_nonneg_of_mem_Icc (x := Real.pi/3*(6-((a+C+3)-b)))
        ⟨by nlinarith only [ha1,hb0,hC1,Real.pi_pos],
          by nlinarith only [hp,le_of_not_gt hn]⟩
      rw [show Real.pi/3*(6-((a+C+3)-b))=2*Real.pi-Real.pi/3*((a+C+3)-b) by ring,
        Real.sin_two_pi_sub] at hs
      linarith only [hs,hc24]
    linarith only [hgap,hb]
  refine ⟨{ angle := ![a,a-B+6,a+C+3,b+A,b],bounds := ?_,phase := ?_ }⟩
  · intro i
    fin_cases i
    · simpa [l38BankBin] using And.intro ha ha1
    · norm_num [l38BankBin]
      exact And.intro h1lo h1hi
    · norm_num [l38BankBin]
      constructor <;> linarith only [h2lo,h2hi]
    · norm_num [l38BankBin]
      exact And.intro h3lo h3hi
    · simpa [l38BankBin] using And.intro hb0 hb
  · intro i
    fin_cases i <;> norm_num
    · exact h0
    · exact hphase1
    · exact hphase2
    · simpa only [add_assoc] using hA
    · exact h4

theorem exists_bank_bin_boundary_of_sharp_pair (ht : G.TriangleFree)
    (hF : F∈G.defectPlaneFaces ht) (ρ : ℝ) (i j : Fin 5) (hne : i≠j)
    (hi : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (P.normal i))
    (hj : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (P.normal j)) :
    ∃ Q : PentagonFaceBoundary G F,Nonempty (Q.BankBinData ρ) := by
  obtain ⟨a,ha0,ha1,hpa⟩ := l38_bank_normal_phase ρ (P.normal i) (P.normal_norm i) hi
  obtain ⟨b,hb0,hb1,hpb⟩ := l38_bank_normal_phase ρ (P.normal j) (P.normal_norm j) hj
  have hab : a≠b := by
    intro h
    exact hne (P.normal_injective ht hF (by rw [← hpa,← hpb,h]))
  have construct (i j : Fin 5) (a b : ℝ) (ha : 0< a) (hab : a< b) (hb : b<1)
      (hi : unitAngleVector (ρ+a)=P.normal i) (hj : unitAngleVector (ρ+b)=P.normal j) :
      ∃ Q : PentagonFaceBoundary G F,Nonempty (Q.BankBinData ρ) := by
    have hjidx := P.bank_phase_pair_predecessor ht hF ρ a b ha hab hb i j hi hj
    refine ⟨P.bankShift i,(P.bankShift i).bank_bin_data_of_bank_pair ht hF ρ a b ha hab hb ?_ ?_⟩
    · simpa only [P.bankShift_normal,add_zero] using hi
    · simpa only [P.bankShift_normal,← hjidx] using hj
  rcases lt_or_gt_of_ne hab with h | h
  · exact construct i j a b ha0 h hb1 hpa hpb
  · exact construct j i b a hb0 h ha1 hpb hpa

end PentagonFaceBoundary
end Swanepoel
