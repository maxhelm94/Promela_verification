mtype = {RED, YELLOW, GREEN};
mtype = {CHANGE};
mtype tl1;
mtype tl2;
bool progress1 = true;
bool progress2 = false;
chan c = [1] of {mtype}
byte turn = 1

/*
Problem c:
No, there is no deadlock state present. Both traffic lights can circle through
their colours an infinite amount of times. We have two LTL formula that
guarantee that our liveness conditions are met. One ensures that both traffic
lights display their colours an infinite amount of times, the other one ensures
that every traffic light will eventually change its colours in the correct sequence.
If we had a deadlock state, then these two conditions would not be met and
spin would make notice when "spin -search -ltl infi ass2_cd.pml" was run.
Potential problems are that both traffic lights could start with a non-red
colour if they are set non-deterministically. Therefore both traffic lights
were set to red in the beginning.

Both proctype 1 and 2 were changed in a way that they have a turn order but
they do not have to wait for each other. If one traffic light is ready to
change from red, then it can continue if the other one remains in the red
state. There is one never loop that guarantees that either traffic light is
red at any given time. 
*/

proctype light2() {
    do
        :: (tl2 == GREEN);
    yellow:     tl2 = YELLOW; printf("traffic light 2 is yellow\n")
        :: (tl2 == YELLOW); 
    red:        printf("traffic light 2 is red\n"); tl2 = RED
                progress2 = false; turn = 1;
                do
                    :: true; break
                    :: true; skip
                od
                progress2 = true;
        :: (tl2 == RED); (tl1 == RED && (progress1 == false || turn == 2));  
    green:      tl2 = GREEN; printf("traffic light 2 is green\n")
    od 
}


proctype light1() {
    do
        :: (tl1 == GREEN);
    yellow:     tl1 = YELLOW; printf("traffic light 1 is yellow\n")
        :: (tl1 == YELLOW); 
    red:        printf("traffic light 1 is red\n"); tl1 = RED
                progress1 = false; turn = 2;
                do
                    :: true; break
                    :: true; skip
                od
                progress1 = true;  
        :: (tl1 == RED); (tl2 == RED && (progress2 == false || turn == 1));
    green:      tl1 = GREEN; printf("traffic light 1 is green\n")
    od 
}

init {
    // for this exercise, we do not start in a non-deterministically chosen
    // state but we will set both traffic lights to RED to avoid immediate
    // conflicts
    tl1 = RED;
    tl2 = RED;
    run light1();
    run light2();
}

// at any given time one of the two traffic lights need to be red
ltl mutex { [] (tl1 == RED || tl2 == RED)}

// a never claim that will fail if both traffic lights display green or yellow
never {
    do
        :: ((light1@yellow || light1@green) && (light2@yellow || light2@green)); break
        :: else
    od
}

// these 2 LTL formulas are the same as the one we used when dealing with only
// one traffic light, expect they were extended to cover both traffic lights
ltl infi { []<> light1@yellow && []<> light1@red && []<> light1@green &&
           []<> light2@yellow && []<> light2@red && []<> light2@green }


ltl pgrss { 
    [] (light1@green -> <> light1@yellow) && [] (light1@yellow -> <> light1@red) &&
    [] (light1@red -> <> light1@green) && [] (light2@green -> <> light2@yellow) &&
    [] (light2@yellow -> <> light2@red) && [] (light2@red -> <> light2@green)
}