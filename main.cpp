#include <iostream>
#include <cstdlib>
#include <cctype>
#include <climits>
#include <cstring>
#include <cmath>
#include <cstdio>

using namespace std;


/* Rabin-Karp algorithm */
void rabin_karp(char *text, unsigned long filesize, char *p, int (*alphafunc)(int))
{
	long mod_p = 0;
	long ts = 0;
	
	char *j;
	int i,k;
	
	short *vals = new short[256];
	memset(vals, 0, 256*sizeof(short));
	
	
	for (i=0, k=0; i<256; i++) {
		if (alphafunc(i))
			vals[i] = k++;
	}
		
	long d = k;
	long q = LONG_MAX/k;
	

	for (i=0, j=p; *j; i++, j++) {
		mod_p = (d*mod_p + vals[p[i]]) % q;
		ts = (d*ts + vals[text[i]]) % q;
	}
	
	
	int p_len = i;
	
	long h = d;
	for (i=0; i<p_len-2; i++)
		h = (h*d) % q;

	
	for (i=0; i<=filesize-p_len; i++) {
		if (mod_p == ts) {
			for (k=0; k<p_len; k++) {
				//cerr<<text[i+k];
				if (p[k] != text[i+k])
					break;
			}
			if (k == p_len)
				cout<<"Pattern found at "<<i<<endl;
		}
		
		//ts = (d*((ts - vals[text[i]]*h)%q) + vals[text[i+p_len]]);
		//ts = ((ts < 0)? q-(-ts%q) : (ts%q) );
		ts = ts - (vals[text[i]]*h)%q;
		ts = d*ts + vals[text[i+p_len]];
		
		//C usually implements truncated modulus we need floored
		//see http://en.wikipedia.org/wiki/Modulo_operator
		ts = ((ts < 0)? q-(-ts%q) : (ts%q) );
	}
	
	
	delete[] vals;
}



/* helper function for DFA, KMP, and Boyer-Moore algorithms */
short * compute_prefix_func(char *p, short len)
{
	short *pi = new short[len];
	short k = 0;
	pi[0] = k;

	for (int q=1; q<len; q++) {
		while (k>0 && p[k]!=p[q])
			k = pi[k-1];
		if (p[k] == p[q])
			k++;
		pi[q] = k;
	}
	return pi;
}


/* DFA matching algorithm */
void automata_matcher(char *text, size_t text_len, char *p)
{
	short len = strlen(p);
	short *trans_func = new short[(len+1)*256];

	short *pi = compute_prefix_func(p, len);
	int alpha_sz = 256;	

	int i;
	for (i=0; i<=len; i++) {
		if (i==0) {
			for (size_t j=0; j<alpha_sz; j++) {
				//cerr<<(char)j<<"\t"<<p[0]<<endl;
				trans_func[j] = (j==p[0])? 1 : 0;
			}
		} else {
			for (size_t j=0; j<alpha_sz; j++) {
				if (j != p[i] || i==len)
					trans_func[i*alpha_sz+j] = trans_func[pi[i-1]*alpha_sz+i];
				else
					trans_func[i*alpha_sz+j] = i+1;
			}
		}

/*
		for (size_t k=0; k<alpha_sz; k++)
			cerr<<trans_func[i*alpha_sz+k]<<"\t";
		cerr<<endl<<endl;
*/
	}

	unsigned char *textu = (unsigned char*)text;
	#define TRANS(q, a) trans_func[q*alpha_sz+a]
	int q = 0;
	for (i=0; i<text_len; i++) {
		q = TRANS(q, textu[i]);
		if (q == len)
			cout<<"Pattern found at "<<i-len+1<<endl;
		//cerr<<q<<"\t";
	}
	#undef TRANS

	delete[] trans_func;
	delete[] pi;
}


/* Knuth-Morris-Pratt algorithm */
void kmp_matcher(char *text, size_t text_len, char *p)
{
	short len = strlen(p);
	short *pi = compute_prefix_func(p, len);
	short q = 0;

	for (int i=0; i<text_len; i++) {
		while (q>0 && p[q]!=text[i])
			q = pi[q-1];
		if (p[q] == text[i])
			q++;
		if (q == len) {
			cout<<"Pattern found at "<<i-len+1<<endl;
			q = pi[q-1];
		}
	}

	delete[] pi;
}


#define ALPHABET_SIZE 128

void prepare_badcharacter_heuristic(const char *str, size_t size, int result[ALPHABET_SIZE])
{
	size_t i;

	for (i = 0; i < ALPHABET_SIZE; i++)
		result[i] = -1;
 
	for (i = 0; i < size; i++)
		result[(size_t) str[i]] = i;
}

/* result is array of size size+1 */
void prepare_goodsuffix_heuristic(const char *normal, size_t size, int result[])
{
	char *left = (char *) normal;
	char *right = left + size;
	char *reversed = new char[size+1];
	char *tmp = reversed + size;
	size_t i,j;
	char test;
 
	/* reverse string */
	*tmp = 0;
	while (left < right)
		*(--tmp) = *(left++);
 
	//int prefix_normal[size];
	short *prefix_reversed = compute_prefix_func(reversed, size);
 
	//compute_prefix(normal, size, prefix_normal);
	//compute_prefix(reversed, size, prefix_reversed);
 
	/* can't figure out how to handle position 0 with the rest
	it's algorithm is slightly different */
	i = 1;
	result[size] = 1;
	while (prefix_reversed[i++])
		result[size]++;
	
	for (i=1; i<size; i++) {
		/*max = 0; */
		test = 0;
		for (j=i; j<size-1; j++) {
			/*if (!test && prefix_reversed[j] == i) */
			
			if (prefix_reversed[j] == i) {
				test = 1;
				if (prefix_reversed[j+1] == 0) {
					test = 2;
					break;
				}
			}
			/* if (prefix_reversed[j] > max) max++; */
		}
		
		if (test == 1)	/*j == size-1 && test) */
			result[size-i] = size;
		else if (test == 2)
			result[size-i] = j+1 - i;
		else
			result[size-i] = size - prefix_reversed[size-1];
	}
	
	//result of 0 will only be accessed when we find a match
	//so it stores the good suffix skip of the first character
	//(last in reverse calculation)
	result[0] = size - prefix_reversed[size-1];
	//The last value in the prefix calculation is always
	//the same for a string in both directions
	
	delete[] prefix_reversed;
	delete[] reversed;
}
/*
 * Boyer-Moore search algorithm
 */
void boyermoore_search(char *haystack, char *needle)
{
	/* Calc string sizes */
	size_t needle_len, haystack_len;
	needle_len = strlen(needle);
	haystack_len = strlen(haystack);
 
	/** Simple checks */
	if(haystack_len == 0)
		return;
	if(needle_len == 0)
		return;
	if(needle_len > haystack_len)
		return;
	
	/** Initialize heuristics */
	int badcharacter[ALPHABET_SIZE];
	int *goodsuffix = new int[needle_len+1];
 
	prepare_badcharacter_heuristic(needle, needle_len, badcharacter);
	prepare_goodsuffix_heuristic(needle, needle_len, goodsuffix);
 
	/** Boyer-Moore search */
	size_t s = 0;
	while(s <= (haystack_len - needle_len))
	{
		size_t j = needle_len;
		while(j > 0 && needle[j-1] == haystack[s+j-1])
			j--;
 
		if(j > 0) {
			int k = badcharacter[(size_t) haystack[s+j-1]];
			int m;
			if(k < (int)j && (m = j-k-1) > goodsuffix[j])
				s+= m;
			else
				s+= goodsuffix[j];
		} else {
			cout<<"Pattern found at "<<s<<endl;
			s += goodsuffix[0];
		}
	}


	delete[] goodsuffix;
}











int main(int argc, char **argv)
{	
	if (argc != 3) {
		cerr<<"Usage ./a.out <text-to-search> <pattern>"<<endl;
		return 0;
	}
	

	FILE *file = fopen(argv[1], "rb");
	fseek(file, 0, SEEK_END);
	size_t size = ftell(file);
	char *text = new char[size+1];
	rewind(file);
	
	int tmp;
	if ((tmp = fread(text, sizeof(char), size, file)) != size)
		cerr<<"read failure\n";


	cout<<"Results for Rabin-Karp:\n";
	rabin_karp(text, size, argv[2], isprint);
		
	cout<<"\nResults for automata_matcher:\n";
	automata_matcher(text, size, argv[2]);

	cout<<"\nResults for Knuth-Morris-Pratt:\n";
	kmp_matcher(text, size, argv[2]);
	
	cout<<"\nResults for Boyer-Moore:\n";
	boyermoore_search(text, argv[2]);

	

	fclose(file);
	delete[] text;
	
	
	return 0;
}
