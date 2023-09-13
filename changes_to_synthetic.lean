/-
Here I will note changes made to the axioms and synthetic:
--2023/9/12
Changed names of I.33 and I.41

--2023/9/10
Changed name of I.37 to area_eq_of_tri. Deleted a bad lemma for the previous I.37

--2023/5/27
Replaced 

  theorem parallelarea {a b c d e f : point} {L M K N O P : line}
  (aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
  (eL: online e L) (fL: online f L)
  (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
  (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
  (par1 : para L M)
    (par3 : para K N) (par4 : para O P) :
    area b a d + area d b c = area c f e + area e c b
with
  theorem area_eq_of_paragram (pgram1 : paragram a d c b L M N O) (pgram2 : paragram e f c b L P N Q)
    : area a d b + area d b c = area e f b + area f b c

--2023/5/11
Replaced 

  theorem parasianar {a b c d : point} {L M N K : line} (aL: online a L) (bL: online b L)
  (cM: online c M) (dM: online d M) (aK: online a K) (cK: online c K) (bN: online b N) (dN: online d N)
  (par1 : para L M) (par2 : para K N) :
    length a b = length c d ∧ angle c a b = angle b d c ∧ area c a b = area b d c
with
  theorem len_ang_area_eq_of_parallelogram (pgram : paragram a b c d M N O P) : 
    length a b = length c d ∧ angle b a d = angle b c d ∧ area a b d = area b c d

Added paragram to the axioms file. This pretty much cleans up some statements. If you need to prove paragram, then you can use the constructor ⟨...⟩ notation to provide the arguments.

Replaced
  theorem sameside_of_online_online_para {a b : point} {M N: line} (aM: online a M) (bM: online b M)(par: para M N) : sameside a b N
with
  theorem sameside_of_para_online (aM : online a M) (bM : online b M) (paraMN : para M N) 
    : sameside a b N

--2023/5/10
Replaced
  theorem drawpar {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
    (aL : ¬online a L) : ∃ (e : point), ∃ (N : line),online e N ∧ online a N ∧ online b L ∧ online c L∧  para N L
with
  theorem para_of_offline (aM : ¬online a M) : ∃ N, online a N ∧ para M N := by

Replaced
  theorem parapostcor {a d g h : point} {L M N : line} (dh : d ≠ h) (aM: online a M) (gM: online g M)
  (hN: online h N) (dN: online d N) (hL : online h L)
    (gL : online g L) (par : para M N) (adL : diffside a d L) : angle a g h = angle g h d :=
with
  theorem alternate_eq_of_para (aM : online a M) (bM : online b M) (bL : online b L) 
    (cL : online c L) (cN : online c N) (dN : online d N) (adL : diffside a d L) 
    (paraMN : para M N) : angle a b c = angle b c d 

Replaced
  theorem online_of_online_para {a : point} {M N: line}(aM: online a M)(par: para M N): 
    ¬ online a N:=
with
theorem offline_of_para (aM : online a M) (paraMN : para M N) : ¬online a N := by 

--2023/5/9
Changed 

  theorem angeqpar {a e f d : point} {L M N : line} (ae : a ≠ e) (ef : e ≠ f) (fd : f ≠ d)
  (aM : online a M) (eM : online e M) (fN : online f N) (dN : online d N)
  (eL : online e L) (fL : online f L) (ang : angle a e f = angle e f d) (adL : diffside a d L) :
  para M N

to 

  theorem para_of_ang_eq (bc : b ≠ c) (aM : online a M) (bM : online b M) (bL : online b L) 
    (cL : online c L) (cN : online c N) (dN : online d N) (adL : diffside a d L) 
    (cba_bcd : angle c b a = angle b c d) : para M N

--2023/5/5
Now with triangle_of_ne_online and asa you can obtain the original statemnt of asa.

--2023/5/4
Replaced

  theorem asa {a b c d e f : point} {L : line} (ef : e ≠ f) (eL : online e L) (fL : online f L)
    (dL : ¬online d L) (side : length b c = length e f) (ang1 : angle c b a = angle f e d)
    (ang2 : angle a c b = angle d f e) :
    length a b = length d e ∧ length a c = length d f ∧ angle b a c = angle e d f

for

  theorem asa (tri_abc : triangle a b c) (tri_def : triangle d e f) (ab_de : length a b = length d e)
      (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) : 
      length a c = length d f ∧ length b c = length e f ∧ angle a c b = angle d f e := 

To get one triangle from the line data, you can use triangle_of_ne_online. For the other you have to work much harder. Don't use this version of synthetic yet, Ian

--2023/4/27

Replaced 

theorem vertang {a b c d e : point} {L : line} (cL : online c L) (dL : online d L)
  (aL : ¬online a L) (Bced : B c e d) (Baeb : B a e b) : angle b e c = angle d e a

with

theorem vertical_angle (Babc : B a b c) (Bdbe : B d b e) (aL : online a L) (bL : online b L)
    (dL : ¬online d L) : angle a b d = angle c b e


--2023/4/24
Got rid of pt_extension_of_ne since it can be deduced from length_eq_B_of_ne

Refactored I.11-14

--2023/4/14
Changed sameside23_of_B123_online1_not_online2 to sameside_of_B_not_online_2

Refactored I.9-10

--2023/4/8
Made an attempt to refactor I.6

Changed
  area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a c b ↔ area a c d + area d c b = area a d b)
to
  area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a b c ↔ area d a b + area d c b = area d a c)

Changed
  area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 → length b c = length b1 c1 →
    length c a = length c1 a1 → area a b c = area a1 b1 c1
to
  area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 →
  length a c = length a1 c1 → length b c = length b1 c1 → area a b c = area a1 b1 c1

Desorrified online_ne_of_line

--2023/4/5

Changed 
  pt_on_circle_of_inside_ne : ∀ {b c : point}, ∀ {α : circle}, b ≠ c →in_circle b α →
  ∃ (a : point), B a b c ∧ on_circle a α
to
  pt_oncircle_of_inside_ne : ∀ {a b : point}, ∀ {α : circle}, a ≠ b → in_circle b α →
  ∃ (c : point), B a b c ∧ on_circle c α

Defined isosceles triangles as iso_tri

Changed same_length_B_of_ne_le to B_length_eq_of_ne_lt

Changed same_length_B_of_ne_four to length_eq_B_of_ne_four. The length in the conclusion is off
by a .symm from the original

Changed 
  theorem same_length_B_of_ne {a b c : point} (hab : a ≠ b) (hbc : b ≠ c) :
  ∃ (p : point), B a b p ∧ length b p = length c b
to
  theorem length_eq_B_of_ne (ab : a ≠ b) (bc : b ≠ c) :
  ∃ (d : point), B a b d ∧ length b c = length b d

Changed difsamedif to diffside_of_sameside_diffside

Ported Euclid I.1-5

Unsorrified online_of_line. Why is the indentation so delicate for this?

Swapped variables in diffside_of_not_online so that we obtain sameside a b L and inputs
are alphabetical
  Before:
    diffside_of_not_online : ∀ {L : line}, ∀ {b : point}, ¬online b L →
    ∃ (a : point), ¬online a L ∧ ¬sameside a b L
  After:
    diffside_of_not_online : ∀ {L : line}, ∀ {a : point}, ¬online a L →
    ∃ (b : point), ¬online b L ∧ ¬sameside a b L

--2023/4/4

Removed all imports except "Euclid.synthetic_axioms", since the axioms import ℝ along with Finite
  already

Changed cen_circ to center_circle

Changed oncircle to on_circle

Changed in_circ to in_circle

Changed
  (circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), on_circle b α ∧ center_circle a α)
to
  (circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), center_circle a α ∧ on_circle b α)
i.e. obtain the center before the point on the circle (also alphabetically more intuitive)

Changed incircle_iff_length_lt to in_circle_iff_length_lt to match on_circle_iff_length_eq

Swapped the first two arguments in in_circle_iff_length_lt
  (in_circle_iff_length_lt : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α → 
  (length a c < length a b ↔ in_circle c α))

Swapped the first two arguments in on_circle_iff_length_eq
  (on_circle_iff_length_eq : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α → 
  (length a b = length a c ↔ on_circle c α))

-/