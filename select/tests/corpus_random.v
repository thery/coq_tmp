(* Differential corpus: 200 random goals (seed 42), written by
   gen_random.sh; each one gets 12 random patterns (random_gen.v). *)
From Stdlib Require Import List.
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support random_gen.
Import ListNotations.
Section Random.
Variables (f : nat -> nat -> nat) (g : nat -> nat).

Goal forall (a b c : nat) (l : list nat), c = (length l) .
intros a b c l.
elpi diff_random "rand.1" "1668674806".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g ((fst (0, (f b c))) + ((snd (2, 3)) * (1 + c)))) = 
(fst ((f (snd ((3 * 0), b)) (f (f a a) (snd (b, c)))), 3)) .
intros a b c l.
elpi diff_random "rand.2" "1341335126".
Abort.

Goal forall (a b c : nat) (l : list nat), (b + ((g c) + (g 0))) = 
(snd ((f (snd ((3 * c), (g c))) (length l)), ((g (fst (a, 1))) + (f (fst (3, b)) (f 0 3))))) 
.
intros a b c l.
elpi diff_random "rand.3" "1109690294".
Abort.

Goal forall (a b c : nat) (l : list nat), (f 2 (f a c)) = 
(f (f ((g 0) * (b * c)) (g (3 + 3))) (fst ((snd (3, a)), (length l)))) .
intros a b c l.
elpi diff_random "rand.4" "318513738".
Abort.

Goal forall (a b c : nat) (l : list nat), (length ((b * (length l)) :: l)) = 
b .
intros a b c l.
elpi diff_random "rand.5" "1047445811".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 1 .
intros a b c l.
elpi diff_random "rand.6" "1590312335".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((fst (b, ((3 * c) * (g a)))) + a) .
intros a b c l.
elpi diff_random "rand.7" "1856591833".
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
(2 + ((snd ((fst (b, c)), (length l))) * (snd ((1 + 3), (3 * 2))))) .
intros a b c l.
elpi diff_random "rand.8" "697675631".
Abort.

Goal forall (a b c : nat) (l : list nat), b = (f (3 + b) c) .
intros a b c l.
elpi diff_random "rand.9" "696523709".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (a :: ((fst (a, b)) :: (l ++ l)))) = 1 .
intros a b c l.
elpi diff_random "rand.10" "1241706392".
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
(length (((c :: l) ++ l) ++ ((1 :: l) ++ l))) .
intros a b c l.
elpi diff_random "rand.11" "477176028".
Abort.

Goal forall (a b c : nat) (l : list nat), (g b) = a .
intros a b c l.
elpi diff_random "rand.12" "1144605537".
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (g c)) * a) = 
((g (fst ((snd (c, a)), (g 0)))) + (g (fst ((snd (2, c)), b)))) .
intros a b c l.
elpi diff_random "rand.13" "936856787".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((f (fst (b, a)) (fst (b, 1))), ((a * b) * 1))) * (fst ((length (l ++ l)), (f (length l) (length l))))) 
= ((g ((length l) + (g 1))) * (((g b) + (2 + 0)) * ((g a) * (b * 0)))) .
intros a b c l.
elpi diff_random "rand.14" "110789419".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = (f a 3) .
intros a b c l.
elpi diff_random "rand.15" "689955794".
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 
(snd (((0 * (3 * a)) * ((snd (1, 0)) * 1)), (f (snd ((fst (0, 2)), 3)) (fst ((snd (1, b)), a))))) 
.
intros a b c l.
elpi diff_random "rand.16" "1078572263".
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (2 + 0)) * (g (g (0 + 1)))) = 
2 .
intros a b c l.
elpi diff_random "rand.17" "2085834609".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (f (fst ((snd (c, c)), (snd (a, a)))) ((length l) + (length l))) (length l)) 
= (fst ((fst ((snd ((length l), (length l))), 2)), 0)) .
intros a b c l.
elpi diff_random "rand.18" "1126901856".
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 1 .
intros a b c l.
elpi diff_random "rand.19" "1737124492".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (c, ((length (l ++ l)) + (g (length l))))) = 
(g (snd (((fst (b, a)) + (fst (1, b))), b))) .
intros a b c l.
elpi diff_random "rand.20" "1139155659".
Abort.

Goal forall (a b c : nat) (l : list nat), a = (g 2) .
intros a b c l.
elpi diff_random "rand.21" "804583764".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = (snd (0, b)) .
intros a b c l.
elpi diff_random "rand.22" "363888031".
Abort.

Goal forall (a b c : nat) (l : list nat), c = b .
intros a b c l.
elpi diff_random "rand.23" "422139067".
Abort.

Goal forall (a b c : nat) (l : list nat), (b * (g ((g 2) + (fst (2, 2))))) = 
(snd ((g ((fst (0, 1)) + (0 * 1))), ((length (c :: l)) * 0))) .
intros a b c l.
elpi diff_random "rand.24" "1341142304".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (length ((a :: l) ++ (0 :: l)))) = (fst (2, (2 * c))) .
intros a b c l.
elpi diff_random "rand.25" "1431909395".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((snd (3, c)) * (length l)) .
intros a b c l.
elpi diff_random "rand.26" "2110410625".
Abort.

Goal forall (a b c : nat) (l : list nat), (length (((l ++ l) ++ l) ++ l)) = 
b .
intros a b c l.
elpi diff_random "rand.27" "818965945".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((l ++ l) ++ (l ++ (l ++ l)))) = b .
intros a b c l.
elpi diff_random "rand.28" "2146114903".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((g (b * 3)), (length (l ++ l)))) * 1) = 
(fst (0, (length ((l ++ l) ++ l)))) .
intros a b c l.
elpi diff_random "rand.29" "1011364468".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((fst ((g 0), 3)) * 2) + ((length (b :: l)) * (f (a * b) (0 + a)))) = 
(length (((fst (a, 1)) :: (l ++ l)) ++ l)) .
intros a b c l.
elpi diff_random "rand.30" "845464616".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (0, (fst (((c + 1) * (c * a)), (fst (0, (fst (a, c)))))))) = 
((f (fst ((g 1), (g 2))) (g 1)) + (a * (g (2 + b)))) .
intros a b c l.
elpi diff_random "rand.31" "1986495558".
Abort.

Goal forall (a b c : nat) (l : list nat), c = a .
intros a b c l.
elpi diff_random "rand.32" "998743762".
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
(0 + ((length l) + (0 * (f c 1)))) .
intros a b c l.
elpi diff_random "rand.33" "1932530020".
Abort.

Goal forall (a b c : nat) (l : list nat), (g 3) = 0 .
intros a b c l.
elpi diff_random "rand.34" "1088871369".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((fst (b, (g (snd (b, a))))), (((snd (b, a)) + a) * (f (length l) (fst (0, b)))))) 
= ((fst (b, (f (fst (c, b)) (fst (2, 0))))) * (fst (3, (f c (length l))))) .
intros a b c l.
elpi diff_random "rand.35" "775918059".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((g ((b + 0) + (length l))) * (g (f (c + 0) (length l)))) = 
(snd ((length (l ++ (a :: l))), c)) .
intros a b c l.
elpi diff_random "rand.36" "1535623716".
Abort.

Goal forall (a b c : nat) (l : list nat), b = 2 .
intros a b c l.
elpi diff_random "rand.37" "1217453200".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((length (c :: l)), (snd ((3 * 3), (length l))))) + (fst (c, ((length l) + c)))) 
= (g (snd ((snd ((f 3 0), (length l))), (length (l ++ l))))) .
intros a b c l.
elpi diff_random "rand.38" "1454681878".
Abort.

Goal forall (a b c : nat) (l : list nat), c = 2 .
intros a b c l.
elpi diff_random "rand.39" "1237624482".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = (g a) .
intros a b c l.
elpi diff_random "rand.40" "1917180815".
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (((g a) + 3), (length l))) = 
(fst ((f 1 (length l)), (snd (((f b 0) + (b * 3)), b)))) .
intros a b c l.
elpi diff_random "rand.41" "996029156".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((f (f 2 c) (snd (b, c))) * (fst ((1 * 2), (g 1)))) + (((1 * a) * (fst (0, 3))) * (length (c :: l)))) 
= (g (g ((snd (1, 1)) + b))) .
intros a b c l.
elpi diff_random "rand.42" "928171362".
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (c, 1)) = 2 .
intros a b c l.
elpi diff_random "rand.43" "1553204197".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((g b) + (length (c :: l))), (((2 * c) * a) + (g (length l))))) = 
(fst (b, (a + (b + (f b 1))))) .
intros a b c l.
elpi diff_random "rand.44" "1294451470".
Abort.

Goal forall (a b c : nat) (l : list nat), (g (length l)) = (0 + 3) .
intros a b c l.
elpi diff_random "rand.45" "389883366".
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
((f (length (1 :: l)) (f c c)) * (length ((1 :: l) ++ (l ++ l)))) .
intros a b c l.
elpi diff_random "rand.46" "485779479".
Abort.

Goal forall (a b c : nat) (l : list nat), a = c .
intros a b c l.
elpi diff_random "rand.47" "1422749363".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 1 .
intros a b c l.
elpi diff_random "rand.48" "1680229135".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (l ++ ((l ++ l) ++ (b :: l)))) = (f (length ((a :: l) ++ l)) 2) .
intros a b c l.
elpi diff_random "rand.49" "156320030".
Abort.

Goal forall (a b c : nat) (l : list nat), (g (fst (0, (a + (0 * 2))))) = 
(fst ((fst ((snd ((0 + 3), (snd (3, 0)))), (fst ((fst (a, a)), (g b))))), ((snd (3, (fst (0, c)))) * ((length l) * 3)))) 
.
intros a b c l.
elpi diff_random "rand.50" "1392749706".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((snd (((a * 1) + (g 2)), (snd ((g c), (f 1 0))))) * 0) .
intros a b c l.
elpi diff_random "rand.51" "99761736".
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 
(length ((f (a * b) (3 * 0)) :: ((0 + a) :: (2 :: l)))) .
intros a b c l.
elpi diff_random "rand.52" "137988177".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (length (l ++ (1 :: l))) (snd ((f (f b 0) c), (snd (2, (length l)))))) = 
(snd ((snd ((2 * (snd (3, c))), (g (3 * c)))), (fst ((length (c :: l)), (g (g 2)))))) 
.
intros a b c l.
elpi diff_random "rand.53" "1926635885".
Abort.

Goal forall (a b c : nat) (l : list nat), b = (snd ((g 3), 3)) .
intros a b c l.
elpi diff_random "rand.54" "535761189".
Abort.

Goal forall (a b c : nat) (l : list nat), (length (0 :: l)) = 1 .
intros a b c l.
elpi diff_random "rand.55" "1418770356".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((g (fst (2, 1))) + ((length l) * 0)) ((length (l ++ l)) * 3)) = 0 .
intros a b c l.
elpi diff_random "rand.56" "759487053".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(g (length ((f 3 3) :: (0 :: l)))) .
intros a b c l.
elpi diff_random "rand.57" "1715966091".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f a c) + (f (1 + (fst (0, 1))) (f b (g c)))) = c .
intros a b c l.
elpi diff_random "rand.58" "1770978135".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((fst (3, (f (snd (2, 2)) (fst (3, a))))), c)) = 
(g ((2 + (snd (c, c))) + (f 2 (f c 2)))) .
intros a b c l.
elpi diff_random "rand.59" "1778009450".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (fst (a, (length l))) .
intros a b c l.
elpi diff_random "rand.60" "33823757".
Abort.

Goal forall (a b c : nat) (l : list nat), 2 = (g b) .
intros a b c l.
elpi diff_random "rand.61" "1135996430".
Abort.

Goal forall (a b c : nat) (l : list nat), (g (length l)) = (g 0) .
intros a b c l.
elpi diff_random "rand.62" "268593704".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((c * (1 + a)) :: (b :: (l ++ l)))) = 2 .
intros a b c l.
elpi diff_random "rand.63" "1606467786".
Abort.

Goal forall (a b c : nat) (l : list nat), (c + 0) = 
(f ((snd ((2 * 0), (f a 1))) * 2) (((length l) * (fst (2, a))) + (length (l ++ l)))) 
.
intros a b c l.
elpi diff_random "rand.64" "582685906".
Abort.

Goal forall (a b c : nat) (l : list nat), a = b .
intros a b c l.
elpi diff_random "rand.65" "756132894".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f (g (snd (0, b))) (a + (3 * 1))) + (g (f 3 (length l)))) = 
(fst ((length ((c :: l) ++ (l ++ l))), ((snd (b, (length l))) + (fst ((snd (1, 3)), (fst (c, 1))))))) 
.
intros a b c l.
elpi diff_random "rand.66" "931565045".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((fst ((0 + 3), (f 1 b))) + (g (0 * 1))) c) = 
(c + (fst (c, (snd (1, (0 * 1)))))) .
intros a b c l.
elpi diff_random "rand.67" "344801632".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((fst (((fst (c, a)) + (f 3 a)), 2)), 1)) = 
((0 + 1) + (snd (3, ((fst (0, b)) * (length l))))) .
intros a b c l.
elpi diff_random "rand.68" "188722599".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (((f a 3) + (fst (2, 0))) * (f (a * c) (f 3 1)))) = (g 0) .
intros a b c l.
elpi diff_random "rand.69" "962239650".
Abort.

Goal forall (a b c : nat) (l : list nat), c = b .
intros a b c l.
elpi diff_random "rand.70" "1625940206".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((g (length l)) * (snd (1, 0))), (f b (snd ((f a c), c))))) = 
(length ((l ++ (2 :: l)) ++ ((3 :: l) ++ (l ++ l)))) .
intros a b c l.
elpi diff_random "rand.71" "2049774594".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(2 * (snd ((g (a * c)), (snd ((snd (b, 3)), (3 * 1)))))) = 
((fst ((snd ((0 * 0), c)), ((g a) * (snd (a, b))))) * (snd (c, (fst ((2 + c), (c * b)))))) 
.
intros a b c l.
elpi diff_random "rand.72" "851562981".
Abort.

Goal forall (a b c : nat) (l : list nat), c = 0 .
intros a b c l.
elpi diff_random "rand.73" "767731553".
Abort.

Goal forall (a b c : nat) (l : list nat), (fst ((fst (c, 1)), 2)) = 
(f (f ((b + 2) * (g 1)) (fst ((g c), (g 0)))) (snd (3, ((fst (c, a)) * (b * 1))))) 
.
intros a b c l.
elpi diff_random "rand.74" "554908968".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (b, (2 + (2 + (snd (1, a)))))) = b .
intros a b c l.
elpi diff_random "rand.75" "2004835274".
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (g (length l))) + c) = 3 .
intros a b c l.
elpi diff_random "rand.76" "954178082".
Abort.

Goal forall (a b c : nat) (l : list nat), (fst (a, 2)) = 
(f (snd (c, b)) ((g (snd (b, 3))) + (snd ((fst (1, 3)), (f a b))))) .
intros a b c l.
elpi diff_random "rand.77" "1445627925".
Abort.

Goal forall (a b c : nat) (l : list nat), (g (snd (c, (f 0 (0 * 0))))) = 
((fst ((snd ((fst (c, 0)), (f 1 0))), (length (b :: l)))) * ((f (0 * 1) (length l)) * (length (l ++ l)))) 
.
intros a b c l.
elpi diff_random "rand.78" "1683133919".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(3 + (snd (2, ((f a 2) * (length l))))) = a .
intros a b c l.
elpi diff_random "rand.79" "2126798640".
Abort.

Goal forall (a b c : nat) (l : list nat), ((g 1) + c) = 
(length ((f (a + c) 1) :: ((0 + 0) :: (l ++ l)))) .
intros a b c l.
elpi diff_random "rand.80" "1754296255".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (snd ((snd ((g b), 1)), 2)) ((snd (c, (length l))) * ((snd (a, 2)) + (3 * 3)))) 
= 
(f (fst (2, (f (fst (2, 0)) (snd (2, c))))) (fst (c, (fst ((snd (b, 3)), (g 1)))))) 
.
intros a b c l.
elpi diff_random "rand.81" "1267362692".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((length (l ++ l)), (f c (fst (a, b))))) * (((0 + a) * (b + c)) + ((a + 0) + (2 + 0)))) 
= c .
intros a b c l.
elpi diff_random "rand.82" "519948443".
Abort.

Goal forall (a b c : nat) (l : list nat), (a + 1) = 
((fst (((g a) * (a + 0)), b)) + c) .
intros a b c l.
elpi diff_random "rand.83" "1815919464".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (((snd (c, 0)) :: l) ++ (l ++ (l ++ l)))) = 
((g (f 2 (length l))) * ((fst (b, b)) + (length (l ++ l)))) .
intros a b c l.
elpi diff_random "rand.84" "1833949360".
Abort.

Goal forall (a b c : nat) (l : list nat), b = (length l) .
intros a b c l.
elpi diff_random "rand.85" "1766969308".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((snd ((f (snd (c, 0)) 3), (snd ((f 1 0), (snd (2, 2)))))), (c * ((g 2) + (snd (a, 0)))))) 
= 3 .
intros a b c l.
elpi diff_random "rand.86" "1033964994".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g ((a + 0) + (snd (b, (length l))))) = 
(((snd (3, (g 0))) * (fst ((length l), (a * c)))) * (length ((1 + 3) :: (l ++ l)))) 
.
intros a b c l.
elpi diff_random "rand.87" "1241330967".
Abort.

Goal forall (a b c : nat) (l : list nat), (g 1) = 
(snd ((3 + (length (l ++ l))), (g (length (l ++ l))))) .
intros a b c l.
elpi diff_random "rand.88" "414006827".
Abort.

Goal forall (a b c : nat) (l : list nat), c = (f 0 c) .
intros a b c l.
elpi diff_random "rand.89" "1293847250".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((((length l) * (2 * 1)) * (f (b + 0) (fst (1, 3)))) * (length l)) .
intros a b c l.
elpi diff_random "rand.90" "1505274832".
Abort.

Goal forall (a b c : nat) (l : list nat), a = b .
intros a b c l.
elpi diff_random "rand.91" "1338291452".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((f (f c 2) ((0 * 2) * (0 * 0))), ((f (snd (c, 3)) 1) + (g 3)))) = 3 .
intros a b c l.
elpi diff_random "rand.92" "1789080546".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((g (fst ((1 * 3), (g 3)))) + (f 2 2)) .
intros a b c l.
elpi diff_random "rand.93" "1227490077".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = b .
intros a b c l.
elpi diff_random "rand.94" "308851737".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((g b) * (2 + (fst ((fst (3, 2)), 1)))) = 
(g ((length (l ++ l)) * (fst (a, 1)))) .
intros a b c l.
elpi diff_random "rand.95" "1948605899".
Abort.

Goal forall (a b c : nat) (l : list nat), (a * 3) = b .
intros a b c l.
elpi diff_random "rand.96" "1960315122".
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 
(snd ((f 1 (snd (0, (g c)))), (f (length l) (snd ((3 * 2), c))))) .
intros a b c l.
elpi diff_random "rand.97" "756627182".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((g (g (length l))), (f (g (c * 2)) a))) = 
(snd (b, ((fst ((f 0 c), (2 + 0))) * (length (l ++ l))))) .
intros a b c l.
elpi diff_random "rand.98" "253009014".
Abort.

Goal forall (a b c : nat) (l : list nat), (g (f 3 (length l))) = c .
intros a b c l.
elpi diff_random "rand.99" "787399758".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((snd ((snd (c, 0)), c)), (length (c :: l)))) + 2) = 3 .
intros a b c l.
elpi diff_random "rand.100" "1788608697".
Abort.

Goal forall (a b c : nat) (l : list nat), b = (length l) .
intros a b c l.
elpi diff_random "rand.101" "1366486901".
Abort.

Goal forall (a b c : nat) (l : list nat), (fst (b, a)) = 
((fst ((g 2), (fst (3, (0 * 0))))) * (length l)) .
intros a b c l.
elpi diff_random "rand.102" "716074347".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (c, (snd (3, ((f 2 c) * (g c)))))) = 
(f (((length l) + (1 * 3)) + 3) (f c (g (fst (a, 2))))) .
intros a b c l.
elpi diff_random "rand.103" "1851899183".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(3 * (g (snd ((fst (2, b)), (fst (2, b)))))) = 
(f ((length (l ++ l)) * c) (fst (0, ((fst (1, 0)) + 2)))) .
intros a b c l.
elpi diff_random "rand.104" "1244051949".
Abort.

Goal forall (a b c : nat) (l : list nat), (fst ((2 * (g 2)), c)) = 
(snd ((f (fst ((length l), (snd (0, a)))) (g (f 3 b))), (((c + 1) * (c + a)) * (f (f 2 c) (length l))))) 
.
intros a b c l.
elpi diff_random "rand.105" "834914178".
Abort.

Goal forall (a b c : nat) (l : list nat), 2 = b .
intros a b c l.
elpi diff_random "rand.106" "1298848206".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((g (snd (a, b))) + ((fst ((f 1 1), c)) * 3)) .
intros a b c l.
elpi diff_random "rand.107" "1717090348".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (b, (length ((l ++ l) ++ (1 :: l))))) = (g (fst (a, 0))) .
intros a b c l.
elpi diff_random "rand.108" "1024153390".
Abort.

Goal forall (a b c : nat) (l : list nat), (g (g 2)) = b .
intros a b c l.
elpi diff_random "rand.109" "1380944456".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f c (g (a + b))) * (snd ((f 1 (a * a)), (g (fst (0, c)))))) = 
(f (f ((c + b) + (g b)) (f (b + 3) (0 + b))) (fst ((f (f 0 c) (f 3 c)), (g 1)))) 
.
intros a b c l.
elpi diff_random "rand.110" "240659637".
Abort.

Goal forall (a b c : nat) (l : list nat), a = 3 .
intros a b c l.
elpi diff_random "rand.111" "1521213233".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(f (snd (1, c)) (g (snd ((length l), a)))) .
intros a b c l.
elpi diff_random "rand.112" "356462330".
Abort.

Goal forall (a b c : nat) (l : list nat), (length ((l ++ (l ++ l)) ++ l)) = 
b .
intros a b c l.
elpi diff_random "rand.113" "1208001362".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (g ((length l) + (snd (b, 3))))) = 3 .
intros a b c l.
elpi diff_random "rand.114" "755549851".
Abort.

Goal forall (a b c : nat) (l : list nat), (1 + (fst (a, c))) = 
(length (((l ++ l) ++ l) ++ ((2 + a) :: (2 :: l)))) .
intros a b c l.
elpi diff_random "rand.115" "556833318".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((g (f b (f 0 c))) + (snd ((g (g 0)), (length (a :: l))))) = ((g 0) + b) .
intros a b c l.
elpi diff_random "rand.116" "1106604531".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 2 .
intros a b c l.
elpi diff_random "rand.117" "283851343".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((snd ((length (a :: l)), (f (snd (1, c)) (b + 1)))) * 3) = 
((f (g (length l)) (g (g c))) * (fst (a, 2))) .
intros a b c l.
elpi diff_random "rand.118" "1603680269".
Abort.

Goal forall (a b c : nat) (l : list nat), b = a .
intros a b c l.
elpi diff_random "rand.119" "461064201".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((snd ((f c 1), ((length l) * (f 2 0)))) * a) = b .
intros a b c l.
elpi diff_random "rand.120" "1963541881".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((snd (c, 0)), (g (length l)))) = a .
intros a b c l.
elpi diff_random "rand.121" "562451204".
Abort.

Goal forall (a b c : nat) (l : list nat), (g 1) = 
(length (l ++ ((b :: l) ++ (a :: l)))) .
intros a b c l.
elpi diff_random "rand.122" "943242283".
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
((snd ((1 * (2 * c)), (length (l ++ l)))) + (f c (length (a :: l)))) .
intros a b c l.
elpi diff_random "rand.123" "1311626641".
Abort.

Goal forall (a b c : nat) (l : list nat), (g ((length (c :: l)) + 0)) = 3 .
intros a b c l.
elpi diff_random "rand.124" "1707869390".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((1 + (fst ((a + 0), b))) * (length ((length l) :: (3 :: l)))) = 
((f ((2 + c) * (length l)) (fst ((length l), 1))) + (f (length (2 :: l)) b)) 
.
intros a b c l.
elpi diff_random "rand.125" "1465778734".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((f 2 3) * (snd (c, b))), a)) = (f (length (c :: (a :: l))) a) .
intros a b c l.
elpi diff_random "rand.126" "167508817".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (length ((c :: l) ++ l)) .
intros a b c l.
elpi diff_random "rand.127" "553267086".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (1 * c) .
intros a b c l.
elpi diff_random "rand.128" "1398889153".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((snd ((snd (c, (0 + 3))), (a + 3))), (length l))) = 
((snd (2, b)) + (f (f (f c 0) (length l)) 3)) .
intros a b c l.
elpi diff_random "rand.129" "551848442".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f 0 ((f (length l) (snd (3, 2))) + b)) = (g a) .
intros a b c l.
elpi diff_random "rand.130" "1810282572".
Abort.

Goal forall (a b c : nat) (l : list nat), ((length (l ++ (l ++ l))) + 3) = 
((g (f (fst (a, c)) (fst (1, 3)))) + b) .
intros a b c l.
elpi diff_random "rand.131" "1527287130".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((snd ((snd ((snd (b, 1)), (g c))), (g (f c b)))), (fst (b, ((snd (c, 1)) + (snd (c, 2))))))) 
= 3 .
intros a b c l.
elpi diff_random "rand.132" "22456162".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (a, (fst (3, (fst ((fst (b, c)), 1)))))) = 
(f (snd (((1 + c) * b), (f (f 0 a) (snd (b, b))))) (g (g (snd (0, 2))))) .
intros a b c l.
elpi diff_random "rand.133" "528842434".
Abort.

Goal forall (a b c : nat) (l : list nat), c = (length l) .
intros a b c l.
elpi diff_random "rand.134" "2091959566".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(fst (2, (g (g (snd (3, a)))))) .
intros a b c l.
elpi diff_random "rand.135" "1666650068".
Abort.

Goal forall (a b c : nat) (l : list nat), b = a .
intros a b c l.
elpi diff_random "rand.136" "385832256".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (0, ((f (a + 2) (snd (0, a))) * (g (snd (1, 0)))))) = 2 .
intros a b c l.
elpi diff_random "rand.137" "1703736809".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f 2 ((length l) * (fst ((a * c), (fst (1, a)))))) = 
(f a (f b (1 + (0 + 1)))) .
intros a b c l.
elpi diff_random "rand.138" "184227830".
Abort.

Goal forall (a b c : nat) (l : list nat), (g (g (c * b))) = 
(f (snd (2, ((snd (a, c)) * (f c a)))) ((length (3 :: l)) * ((f 0 3) * (g 1)))) 
.
intros a b c l.
elpi diff_random "rand.139" "1234783882".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((g (3 + c)) * (g (f 3 a))) * (fst (3, a))) = 0 .
intros a b c l.
elpi diff_random "rand.140" "885181163".
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (a, (fst (b, (snd (b, 0)))))) 
= (snd (2, 0)) .
intros a b c l.
elpi diff_random "rand.141" "1561347291".
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
((snd ((length (l ++ l)), (g a))) * (1 + (snd ((snd (a, a)), (fst (c, b)))))) 
.
intros a b c l.
elpi diff_random "rand.142" "1852517734".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((fst ((0 * (fst (2, 1))), ((fst (1, 1)) * (fst (2, 3))))), (length ((l ++ l) ++ (a :: l))))) 
= 
((1 * (snd (b, (a + b)))) * (snd ((fst ((2 * c), (snd (c, 0)))), (snd ((1 * 0), 3))))) 
.
intros a b c l.
elpi diff_random "rand.143" "938573994".
Abort.

Goal forall (a b c : nat) (l : list nat), a = (a * (f b 0)) .
intros a b c l.
elpi diff_random "rand.144" "116309584".
Abort.

Goal forall (a b c : nat) (l : list nat), (fst ((g 3), 1)) = 0 .
intros a b c l.
elpi diff_random "rand.145" "616302440".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((2 + 1) :: (l ++ (2 :: l)))) = 
(f (snd ((snd (a, (fst (a, 3)))), ((f 1 b) * 3))) a) .
intros a b c l.
elpi diff_random "rand.146" "1455216719".
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 3 .
intros a b c l.
elpi diff_random "rand.147" "1276684907".
Abort.

Goal forall (a b c : nat) (l : list nat), (fst (2, 3)) = 
(fst (((length l) * 2), a)) .
intros a b c l.
elpi diff_random "rand.148" "443184140".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (a * ((2 * c) + b)) ((length (l ++ l)) + a)) = 3 .
intros a b c l.
elpi diff_random "rand.149" "327952837".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((fst ((g 1), (length l))) + (g 1)), 3)) = 
((f (3 * 3) 0) * (fst ((snd (2, 2)), 1))) .
intros a b c l.
elpi diff_random "rand.150" "818703593".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((snd ((length (l ++ l)), (c + (f 1 a)))) + 1) = 
(length (((f b 2) :: (l ++ l)) ++ ((length l) :: (l ++ l)))) .
intros a b c l.
elpi diff_random "rand.151" "1566311451".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (snd ((f 3 (g 2)), (snd ((g 3), (snd (a, 3))))))) = 1 .
intros a b c l.
elpi diff_random "rand.152" "631068122".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g ((length l) + (length (c :: l)))) = (3 * (length (a :: (l ++ l)))) .
intros a b c l.
elpi diff_random "rand.153" "1647146997".
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (c, b)) = a .
intros a b c l.
elpi diff_random "rand.154" "338569668".
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
(fst ((snd (1, (g a))), (((f 0 3) + (snd (a, c))) * (length (l ++ l))))) .
intros a b c l.
elpi diff_random "rand.155" "706169699".
Abort.

Goal forall (a b c : nat) (l : list nat), (f (f b a) (f 1 (snd ((g 2), 0)))) 
= ((fst ((g (a + 3)), (g (snd (1, 0))))) * 1) .
intros a b c l.
elpi diff_random "rand.156" "2141259969".
Abort.

Goal forall (a b c : nat) (l : list nat), (f (g (g (c * 0))) c) = 
(f (fst (a, 2)) 3) .
intros a b c l.
elpi diff_random "rand.157" "702325809".
Abort.

Goal forall (a b c : nat) (l : list nat), b = (length l) .
intros a b c l.
elpi diff_random "rand.158" "2057720429".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((fst ((length (c :: l)), b)), ((length (l ++ l)) * (f 1 (f b a))))) = 
(f (g a) a) .
intros a b c l.
elpi diff_random "rand.159" "183975551".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((fst ((b + a), a)) + (snd ((3 + c), 2))) * (f 0 (f c (fst (a, 2))))) = 
(fst ((snd ((snd ((1 + 2), (b * 3))), (length l))), c)) .
intros a b c l.
elpi diff_random "rand.160" "1002089339".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 2 .
intros a b c l.
elpi diff_random "rand.161" "1203668055".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((c * (fst ((f a a), (snd (2, a))))), (length l))) = 
(g (f (fst ((a + a), (fst (a, 0)))) (snd ((length l), (f b 1))))) .
intros a b c l.
elpi diff_random "rand.162" "1707737706".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (snd ((c + (length l)), ((snd (1, a)) + (fst (0, 0))))) a) = 
(c + (snd ((0 + (fst (0, 2))), (fst (3, 2))))) .
intros a b c l.
elpi diff_random "rand.163" "1650019180".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (fst (0, b)) .
intros a b c l.
elpi diff_random "rand.164" "524017687".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((length l) :: (b :: (l ++ l)))) = 0 .
intros a b c l.
elpi diff_random "rand.165" "1337054629".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f 3 (fst ((c * 1), 2))) * (fst ((g b), (snd (0, (f 3 0)))))) = 0 .
intros a b c l.
elpi diff_random "rand.166" "268121591".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (((f 0 3) + (0 + b)) :: ((g 3) :: l))) = 
(g (1 * (1 + (snd (3, a))))) .
intros a b c l.
elpi diff_random "rand.167" "1920401022".
Abort.

Goal forall (a b c : nat) (l : list nat), (c * 2) = 
((fst ((snd (a, (c * 1))), 0)) + 2) .
intros a b c l.
elpi diff_random "rand.168" "1557368527".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((f (a * 2) (b + 0)) * (length (3 :: l))) + c) = (length l) .
intros a b c l.
elpi diff_random "rand.169" "1813760447".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((fst ((f b 0), 2)) * (g (length l))) (length ((length l) :: (1 :: l)))) 
= (g ((length (l ++ l)) + (snd ((f 0 3), c)))) .
intros a b c l.
elpi diff_random "rand.170" "106108756".
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (3, (g (g (3 * b))))) = b .
intros a b c l.
elpi diff_random "rand.171" "2131938122".
Abort.

Goal forall (a b c : nat) (l : list nat), (f b ((f 3 (fst (a, b))) * (g 0))) 
= b .
intros a b c l.
elpi diff_random "rand.172" "1781418277".
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
((fst (((1 + 2) + (f 2 c)), (snd ((length l), (snd (0, 1)))))) * (length l)) 
.
intros a b c l.
elpi diff_random "rand.173" "1433322139".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 3 .
intros a b c l.
elpi diff_random "rand.174" "518843767".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((g 2) * ((snd (2, 3)) * 0)) .
intros a b c l.
elpi diff_random "rand.175" "1624683905".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(0 * (snd ((fst ((c * c), 0)), (g b)))) = c .
intros a b c l.
elpi diff_random "rand.176" "1362182296".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((length ((l ++ l) ++ (2 :: l))) + ((length (l ++ l)) * (f (1 * 2) (g c)))) 
= (f (f ((g 3) * c) b) (length (l ++ l))) .
intros a b c l.
elpi diff_random "rand.177" "488389132".
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (0, c)) = 
(length ((length (l ++ l)) :: l)) .
intros a b c l.
elpi diff_random "rand.178" "529919938".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (1, (f ((g 1) + (f 1 a)) (g (g c))))) = 
(g ((fst ((length l), (length l))) + (3 * (f a 2)))) .
intros a b c l.
elpi diff_random "rand.179" "1174771914".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(fst (3, (fst ((c * (fst (c, 2))), (g (fst (c, 2))))))) .
intros a b c l.
elpi diff_random "rand.180" "899532922".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((g (fst (b, c))) * (f (2 * a) (c + 2))) (((f 3 1) * a) * 3)) = (0 + 3) .
intros a b c l.
elpi diff_random "rand.181" "47219145".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (snd (1, (fst (2, (fst (2, a))))))) = (g (g ((1 * b) + (snd (c, 2))))) .
intros a b c l.
elpi diff_random "rand.182" "2077599532".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(b + (g (fst ((1 * a), (length l))))) = (c + 2) .
intros a b c l.
elpi diff_random "rand.183" "975220270".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((length (l ++ (3 :: l))) + ((snd ((0 * a), (g b))) * a)) .
intros a b c l.
elpi diff_random "rand.184" "1177180351".
Abort.

Goal forall (a b c : nat) (l : list nat), (c * (f 3 2)) = c .
intros a b c l.
elpi diff_random "rand.185" "1073616781".
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (2 + 2)) + b) = (snd (0, 3)) .
intros a b c l.
elpi diff_random "rand.186" "898180519".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
(fst (2, ((fst ((c + c), 1)) * (f 1 (snd (2, 1)))))) .
intros a b c l.
elpi diff_random "rand.187" "1197629549".
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(f ((length l) + (f 0 (snd (2, 0)))) 2) .
intros a b c l.
elpi diff_random "rand.188" "104498055".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((f (fst (c, 1)) ((a * 1) * (snd (0, c)))), ((fst ((snd (0, c)), (c + 3))) + 1))) 
= (fst (2, (snd ((a + 0), (length (l ++ l)))))) .
intros a b c l.
elpi diff_random "rand.189" "1631607218".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (3, ((snd ((length l), (f 2 c))) * a))) = (f 1 (g (g (g 3)))) .
intros a b c l.
elpi diff_random "rand.190" "1737719216".
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (c, (g (length (2 :: l))))) = 
(f (fst ((fst (c, (fst (3, 0)))), a)) (fst ((g (a + a)), (snd ((b * c), (fst (2, 3))))))) 
.
intros a b c l.
elpi diff_random "rand.191" "552786701".
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((length ((length l) :: (l ++ l))) + 2) .
intros a b c l.
elpi diff_random "rand.192" "1144492058".
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst (3, (f (length l) (c + 1)))) * (g (fst ((b * 3), (snd (a, 2)))))) = b .
intros a b c l.
elpi diff_random "rand.193" "4660657".
Abort.

Goal forall (a b c : nat) (l : list nat), c = (b + (g 2)) .
intros a b c l.
elpi diff_random "rand.194" "166908393".
Abort.

Goal forall (a b c : nat) (l : list nat), (g 1) = 2 .
intros a b c l.
elpi diff_random "rand.195" "504963962".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((f (0 + 0) 1) + (length (1 :: l))), c)) = 3 .
intros a b c l.
elpi diff_random "rand.196" "444055573".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = (length (1 :: l)) .
intros a b c l.
elpi diff_random "rand.197" "295957092".
Abort.

Goal forall (a b c : nat) (l : list nat), ((g c) * (length ((l ++ l) ++ l))) 
= 
(fst ((f ((g c) + (length l)) (f (a * b) (c * 3))), ((fst ((1 + 0), (snd (b, 2)))) * (snd (b, 3))))) 
.
intros a b c l.
elpi diff_random "rand.198" "1498222818".
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
(((length (l ++ l)) + a) + ((fst ((g 3), (2 + a))) + (f 1 c))) .
intros a b c l.
elpi diff_random "rand.199" "943352286".
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (1 + (snd ((snd (c, c)), (snd (c, 2)))))) = 3 .
intros a b c l.
elpi diff_random "rand.200" "485355603".
Abort.

End Random.
