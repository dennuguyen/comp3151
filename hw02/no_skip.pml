byte x = 0;

active proctype P() {
    x = 1;
    x = 2;
}

ltl skip_2 { <>(x == 1 until x == 3) }