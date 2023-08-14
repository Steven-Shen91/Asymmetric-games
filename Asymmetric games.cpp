// Prisoners Dilemma game on a small-world graph constructed from a square lattice
// Some players are blocked to give their strategy (other players cannot adopt their strategy)

// standard include
#include <iostream>
#include <fstream>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>
#include <time.h>
//#include <windows.h>
using namespace std;

// define priority classes
#define NORMAL_PRIORITY_CLASS       0x00000020
#define IDLE_PRIORITY_CLASS         0x00000040
#define HIGH_PRIORITY_CLASS         0x00000080
#define REALTIME_PRIORITY_CLASS     0x00000100

// define parameters
#define L           100      /* lattice size                   */
#define SIZE        (L*L)    /* number of sites                */
#define MC_STEPS    100000   /* run-time in MCS     */
//#define r               /* temptation to defect */
#define K           0.1      /* temperature */
#define Q           0      /* Q portion of links are rewired */
#define NAMEOUT     "K4b075r5Q2"
#define RANDOMIZE   3145215

int defector, cooperator, bdefector, bcooperator, scooperator, sdefector;
int    Coo0, Def0, Coo1, Def1;
double bsmall, bbig;
double cost = 1;
double degree;
int N;
double alpha ;
double gamma1;



typedef int       tomb1[SIZE];
typedef long int  tomb3[SIZE][4];
typedef double    tomb4[SIZE];

tomb1 player_s;           /* matrix ,containing players strategies */
tomb3 player_n;           /* matrix, containing players neighbours */
tomb1 type;

void prodgraph(void);      /* creates host graph                    */
void initial(void);        /* initial state                         */
void game(void);
void tongji(void);
double payoff(int i);

ofstream outfile1;
ofstream outfile2;


/*************************** RNG procedures ****************************************/
#define NN 624
#define MM 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[NN]; /* the array for the state vector  */

static int mti = NN + 1; /* mti==NN+1 means mt[NN] is not initialized */
void sgenrand(unsigned long seed) {
	int i;
	for (i = 0; i < NN; i++) {
		mt[i] = seed & 0xffff0000;
		seed = 69069 * seed + 1;
		mt[i] |= (seed & 0xffff0000) >> 16;
		seed = 69069 * seed + 1;
	}
	mti = NN;
}

void lsgenrand(unsigned long seed_array[]) {
	int i;
	for (i = 0; i < NN; i++)
		mt[i] = seed_array[i];
	mti = NN;
}

double genrand() {
	unsigned long y;
	static unsigned long mag01[2] = {0x0, MATRIX_A};
	if (mti >= NN) {
		int kk;
		if (mti == NN + 1)
			sgenrand(4357);
		for (kk = 0; kk < NN - MM; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + MM] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		for (; kk < NN - 1; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + (MM - NN)] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		y = (mt[NN - 1] & UPPER_MASK) | (mt[0] & LOWER_MASK);
		mt[NN - 1] = mt[MM - 1] ^ (y >> 1) ^ mag01[y & 0x1];
		mti = 0;
	}
	y = mt[mti++];
	y ^= TEMPERING_SHIFT_U(y);
	y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
	y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C;
	y ^= TEMPERING_SHIFT_L(y);
	return y;
}

double randf() {
	return ( (double)genrand() * 2.3283064370807974e-10 );
}

long randi(unsigned long LIM) {
	return ((unsigned long)genrand() % LIM);
}

/********************** END of RNG ************************************/

void initial(void) {
	int i, j;
	int count, Count;
	cooperator = 0;
	defector = 0;


	for (i = 0; i < SIZE; i++) {

		type[i] = 0;
		player_s[i] = (int)randi(2);
		if (player_s[i] == 0)
			cooperator++;
		else
			defector++;
	}

	for (i = 0; i < N; i++) {
		do {
			j = (int)randi(SIZE);

			if (type[j] == 0)
				break;
		} while (1);

		type[j] = 1;
		count++;
	}

}



// creates first a square grid graph and then rewires Q links
void prodgraph(void) {
	int nneighbor, iu, ju, neighbor1, neighbor2;
	long int rewire, first, player1, player2, player3, MCe;
	double x;
	int i, j;


	// set up an initial square lattice
	for (i = 0; i < L; i++) {
		for (j = 0; j < L; j++) {
			// the first player
			player1 = L * j + i;

			// and its four nearest neighbors
			iu = i + 1;
			ju = j;
			if (iu == L)
				iu = 0;
			player2 = L * ju + iu;
			player_n[player1][0] = player2;

			iu = i;
			ju = j + 1;
			if (ju == L)
				ju = 0;
			player2 = L * ju + iu;
			player_n[player1][1] = player2;

			iu = i - 1;
			ju = j;
			if (i == 0)
				iu = L - 1;
			player2 = L * ju + iu;
			player_n[player1][2] = player2;

			iu = i;
			ju = j - 1;
			if (j == 0)
				ju = L - 1;
			player2 = L * ju + iu;
			player_n[player1][3] = player2;
		}
	}

	// the rewiring starts - Q portion of joints is chosen randomly
	x = (double) (1.0 - Q);
	x = - log ( x );
	x = x * (2 * SIZE);
	MCe = (long int) x;


	first = randi(SIZE);
	nneighbor = randi(4);
	player1 = player_n[first][nneighbor];
	neighbor1 = (nneighbor + 2) % 4;

	for (rewire = 0; rewire < MCe - 1; rewire++) {
		do
			player2 = randi(SIZE);
		while (player2 == first || player2 == player1);
		do {
			neighbor2 = randi(4);
			player3 = player_n[player2][neighbor2];
		} while (player3 == first || player3 == player1);
		player_n[player1][neighbor1] = player2;
		player_n[player2][neighbor2] = player1;
		player1 = player3;
		if (player_n[player3][0] == player2)
			neighbor1 = 0;
		if (player_n[player3][1] == player2)
			neighbor1 = 1;
		if (player_n[player3][2] == player2)
			neighbor1 = 2;
		if (player_n[player3][3] == player2)
			neighbor1 = 3;
	}

	player_n[player1][neighbor1] = first;
	player_n[first][nneighbor] = player1;

	//cout<<player1<<'\t'<<player_n[player1][neighbor1]<<endl;

}

///////////////////////////payoff
double payoff(int i) {
	int j;
	int strat1, strat2;
	int player1, player2;
	double P1, P2, F1, F2, score;
	int player11;
	int strat11;



	player1 = i;

	strat1 = player_s[player1];
	score = 0;
	if (type[player1] == 0) {
		for (j = 0; j < 4; j++) {
			player2 = player_n[player1][j];
			strat2 = player_s[player2];
			if (type[player2] == 0) {
				switch (2 * strat1 + strat2) {
					case 0:
						score = score + bsmall - 0.5 * cost;
						break;
					case 1:
						score = score + bsmall - cost;
						break;
					case 2:
						score = score + bsmall;
						break;
					case 3:
						score = score + 0.0;
						break;
				}
			} else {
				switch (2 * strat1 + strat2) {
					case 0:
						score = score + bsmall - gamma1 * cost;
						break;
					case 1:
						score = score + bsmall - cost;
						break;
					case 2:
						score = score + bsmall;
						break;
					case 3:
						score = score + 0;
						break;
				}
			}
		}
	} else {
		for (j = 0; j < 4; j++) {
			player2 = player_n[player1][j];
			strat2 = player_s[player2];
			if (type[player2] == 0) {
				switch (2 * strat1 + strat2) {
					case 0:
						score = score + bbig - (1 - gamma1) * cost;
						break;
					case 1:
						score = score + bbig - cost;
						break;
					case 2:
						score = score + bbig;
						break;
					case 3:
						score = score + 0;
						break;
				}
			} else {
				switch (2 * strat1 + strat2) {
					case 0:
						score = score + bbig - 0.5 * cost;
						break;
					case 1:
						score = score + bbig - cost;
						break;
					case 2:
						score = score + bbig;
						break;
					case 3:
						score = score + 0;
						break;
				}
			}
		}
	}

	return score;

}

//////////////////////////////////
void game(void) {
	int i, j;
	int strat1, strat2;
	int player1, player2;
	double P1, P2, F1, F2;
	int player11;
	int strat11;
	int suiji;
	double p, dP;
	double qqqq;

	for (i = 0; i < SIZE; i++) {
		player1 = (int) randi(SIZE);

		strat1 = player_s[player1];

		suiji = randi(4);

		player2 = player_n[player1][suiji];

		strat2 = player_s[player2];

		P1 = payoff(player1);
		P2 = payoff(player2);

		//Szarbo rule
		if (strat1 != strat2) {
			dP = P1 - P2;
			p = 1 / (1 + exp(dP / K));
			qqqq = randf();
			if (qqqq < p)
				player_s[player1] = strat2;
		}


	}//end of the SIZE

}

void tongji(void) {
	int i;
	cooperator = 0;
	defector = 0;
	scooperator = bcooperator = sdefector = bdefector = 0;
	for (i = 0; i < SIZE; i++) {
		if (player_s[i] == 0 && type[i] == 0)
			scooperator++;
		if (player_s[i] == 0 && type[i] == 1)
			bcooperator++;
		if (player_s[i] == 1 && type[i] == 0)
			sdefector++;
		if (player_s[i] == 1 && type[i] == 1)
			bdefector++;
	}
	cooperator = scooperator + bcooperator;
	defector = sdefector + bdefector;
}

// the main program
int main() {
	int steps;
	double aa, bb, cc, dd, ee, ff, x, XX, x1, scXX, bcXX, sdYY, bdYY, smallc, smalld, bigc, bigd, YY;


	outfile1.open("frequency.txt");
	outfile2.open("average.txt");

	if (!outfile1) {
		cout << "can not open";
		abort();
	}

	if (!outfile2) {
		cout << "can not open";
		abort();
	}

	// initialize the random number generation
	sgenrand(RANDOMIZE);

	prodgraph();





	// begins the mc steps
	for (alpha = 0.0; alpha <= 1.001; alpha = alpha + 0.025) {

		for (gamma1 = 0.0; gamma1 <= 1.01; gamma1 = gamma1 + 0.025) {
			degree = 2;
			bsmall = 0.85;
			N = (int)(alpha * SIZE);
//  	cout<<N<<endl;
			bbig = bsmall * degree;
			aa = bb = cc = dd = ee = ff = 0;
			x = x1 = smallc = smalld = bigc = bigd = 0;
			XX = 0;
			YY = 0;
			scXX = 0;
			sdYY = 0;
			bcXX = 0;
			bdYY = 0;

			initial();
			for (steps = 0; steps < MC_STEPS; steps++) {

				game();
				tongji();



				x = (double)cooperator / SIZE;
				x1 = (double)defector / SIZE;
				smallc = (double)scooperator / SIZE;
				smalld = (double)sdefector / SIZE;
				bigc = (double)bcooperator / SIZE;
				bigd = (double)bdefector / SIZE;

				if (steps % 100 == 0) {
					outfile1 << steps << '\t' << smallc << '\t' << smalld << '\t' << bigc << '\t' << bigd << endl; //<<x<<'\t'<<x1<<endl;
				}




				if (steps > MC_STEPS - 5001) {
					aa += x;
					XX = (double)aa / 5000;
					bb += x1;
					YY = (double)bb / 5000;
					cc += smallc;
					scXX = (double)cc / 5000;
					dd += smalld;
					sdYY = (double)dd / 5000;
					ee += bigc;
					bcXX = (double)ee / 5000;
					ff += bigd;
					bdYY = (double)ff / 5000;
				}

			}//end of the MC steps
			outfile2 << alpha << '\t' << degree << '\t' << gamma1 << '\t' << XX << '\t' << YY << '\t' << scXX << '\t' << bcXX <<
			         '\t' << sdYY << '\t' << bdYY << '\t' << scXX / (scXX + sdYY) << '\t' << bcXX / (bcXX + bdYY) << endl;
			cout << bsmall << '\t' << alpha << '\t' << degree << '\t' << XX << '\t' << YY << '\t' << scXX << '\t' << bcXX << '\t' <<
			     sdYY << '\t' << bdYY << '\t' << scXX / (scXX + sdYY) << '\t' << bcXX / (bcXX + bdYY) << endl;
		}

	}
	outfile1.close();
	outfile2.close();

	return 0;
}



