mtype = {RED, YELLOW, GREEN};
mtype = {CHANGE};
mtype tl1;
mtype tl2;
bool progress1 = true;
bool progress2 = false;
chan c = [1] of {mtype}
byte turn = 1




proctype light2() {
    do
        :: (tl2 == GREEN);
    yellow:     tl2 = YELLOW; printf("traffic light 2 is yellow\n")
        :: (tl2 == YELLOW); 
                // read message into channel c to indicate a traffic light 
                // can cycle through its colours again
    red:        tl2 = RED; printf("traffic light 2 is red\n");
                progress2 = false; turn = 1;
                do
                    :: true; break
                    :: true; skip
                od
                // only progress if we can remoce a message from the channel c
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
                // read message into channel c to indicate a traffic light 
                // can cycle through its colours again
    red:        tl1 = RED; printf("traffic light 1 is red\n")
                progress1 = false; turn = 2;
                do
                    :: true; break
                    :: true; skip
                od
                // only progress if we can remoce a message from the channel c
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

// a never claim that will fail when both traffic lights display green or yellow
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