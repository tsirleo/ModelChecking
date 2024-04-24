/* Variant 18 */
/* 
   Имеется семилитровый сосуд, заполненный до краев водой.
   Также имеется два пустых сосуда на 3 и 4 литра. 
   Как за 4 переливания сделать так, чтобы в сосуде на 3 литра было 2 литра воды? 
*/

#define Seven 7
#define Three 3
#define Four 4
#define Goal 2

int pot7l = Seven;
int pot3l = 0;
int pot4l = 0;
int counter = 0;
int amount;

active proctype main() {
    do
    :: (pot7l > 0 && pot3l < Three) -> atomic { 
        if
        :: ((Three - pot3l) < pot7l) -> atomic { amount = Three - pot3l }
        :: else -> atomic { amount = pot7l }
        fi
        pot7l = pot7l - amount;
        pot3l = pot3l + amount;
        counter++;
        printf("Pour %d liters from 7L pot to 3L pot\n", amount);
    }
    :: (pot3l > 0 && pot7l < Seven) -> atomic { 
        if
        :: ((Seven - pot7l) < pot3l)-> atomic { amount = Seven - pot7l }
        :: else -> atomic { amount = pot3l }
        fi
        pot7l = pot7l + amount;
        pot3l = pot3l - amount;
        counter++;
        printf("Pour %d liters from 3L pot to 7L pot\n", amount);
    }
    :: (pot7l > 0 && pot4l < Four) -> atomic { 
        if
        :: ((Four - pot4l) < pot7l)-> atomic { amount = Four - pot4l }
        :: else -> atomic { amount = pot7l }
        fi
        pot7l = pot7l - amount;
        pot4l = pot4l + amount;
        counter++;
        printf("Pour %d liters from 7L pot to 4L pot\n", amount);
    }
    :: (pot4l > 0 && pot7l < Seven) -> atomic { 
        if
        :: ((Seven - pot7l) < pot4l)-> atomic { amount = Seven - pot7l }
        :: else -> atomic { amount = pot4l }
        fi
        pot7l = pot7l + amount;
        pot4l = pot4l - amount;
        counter++;
        printf("Pour %d liters from 4L pot to 7L pot\n", amount);
    }
    :: (pot3l > 0 && pot4l < Four) -> atomic { 
        if
        :: ((Four - pot4l) < pot3l)-> atomic { amount = Four - pot4l }
        :: else -> atomic { amount = pot3l }
        fi
        pot3l = pot3l - amount;
        pot4l = pot4l + amount;
        counter++;
        printf("Pour %d liters from 3L pot to 4L pot\n", amount);
    }
    :: (pot4l > 0 && pot3l < Three) -> atomic { 
        if
        :: ((Three - pot3l) < pot4l)-> atomic { amount = Three - pot3l }
        :: else -> atomic { amount = pot4l }
        fi
        pot3l = pot3l + amount;
        pot4l = pot4l - amount;
        counter++;
        printf("Pour %d liters from 4L pot to 3L pot\n", amount);
    }
    od;
}

ltl goalNotReached {
    !(<>(pot3l == Goal && counter == Four))
}

