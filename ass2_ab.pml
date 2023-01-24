mtype = {RED, YELLOW, GREEN};
mtype = {CHANGE};
mtype state;
chan c = [1] of {mtype}

// start proctype will non-deterministically choose the beginning state of the
// traffic light 
proctype start() {
    if 
        :: true; state = GREEN
        :: true; state = YELLOW
        // if we start with red, we need to read CHANGE into our channel c to
        // be able remove the message later, when we change colour
        :: true; state = RED; c ! CHANGE
    fi
}


// we run light in an infinite while loop and change the colour of the
// variable "state" according to the current colour; depending on the 
// current colour, we set up labels that indicate the colour and allow us
// to run the LTL formulas that check if our liveness conditions are met
proctype light() {
    do
        :: (state == GREEN);
    yellow:     state = YELLOW; printf("traffic light is yellow\n")
        :: (state == YELLOW); 
                // read message into channel c to indicate a traffic light 
                // can cycle through its colours again
                c ! CHANGE;
    red:        state = RED; printf("traffic light is red\n")
                do
                    :: true; break
                    :: true; skip
                od
        :: (state == RED);
                // only progress if we can remoce a message from the channel c
                c ? CHANGE;  
    green:      state = GREEN; printf("traffic light is green\n")
    od 
}


init {    
    // assigning a colour randomly to the state
    run start();
    // wait until state was assigned
    (_nr_pr == 1);
    // then run light
    run light();
}

// for both ltl formulas we use labels to identify the colour, which the 
// traffic light displays

// this ltl formula called "progress" checks, whether light eventually changes
// colours in the specified sequence (therefore pogresses onwards);
// at any point, light needs to eventually change its state from green to
// yellow, yellow to red and red to green
ltl pgrss { 
    [] ((light@green -> <> light@yellow) && (light@yellow -> <> light@red) &&
        (light@red -> <> light@green))
}

// this ltl formula called infi (for infinity) checks if all colours (states)
// appear infinitely often;
// it uses the GF operators to make sure that at any state there will be 
// a state of every colour in the future.
// (GF yellow) AND (GF red) AND (GF green)
ltl infi { []<> light@yellow && []<> light@red && []<> light@green
}