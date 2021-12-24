/*////////////////////////////////////////////////////
/						 _______	 ________		 /
/			/\			|			|				 /
/		   /  \			|			|				 /
/		  /    \		|			|				 /
/		 /		\		|_______	|________		 /
/		/--------\		|					 |		 /
/	   /		  \		|				     |		 /
/	  /			   \	|					 |		 /	
/	 /				\	|_______	_________|	     /	
/													 /
////////////////////////////////////////////////////*/

//takes 128 bit key size with 10 rounds of expansion
//creates 128 bit blocks of the input text for encryption
//uses SRFG(Symmetric Random Function Generator) to secure AES


#pragma GCC optimize("O3","unroll-loops","omit-frame-pointer","inline") //Optimization flags
#pragma GCC option("arch=native","tune=native","no-zeroupper") //Enable AVX
#pragma GCC target("avx","popcnt")  //Enable AVX
#include <x86intrin.h> //SSE Extensions
#include <bits/stdc++.h> 
#include <random>
using namespace std;
#define eb emplace_back
#define mp make_pair
#define hello cout<<"hello"<<"\n"
#define forr(i,a,b) for(int i=a;i<b;i++)
#define it(s)	for(auto itr:s)
#define dvg(s) 	for(auto itr:s)	cout<<itr<<" ";cout<<endl;
#define dbg(s)	cout<<#s<<"= "<<s<<endl;
typedef long long int lli;

vector<vector<int>> s_box(16,vector<int> (16,0));
vector<int> round_constant{1,2,4,8,16,32,64,128,27,54};
int rounds=0;
string dectohex(vector<int> &state){
	string ret="";
	for(int i=0;i<state.size();i++){
		int a=state[i];
		std::stringstream ss;
		ss<<std::hex<<a;
		string res(ss.str());
		if(res.size()!=2) res="0"+res;
		ret=ret+res;
	}
	return ret;
}


int hextodec(string str){
	int ret=0;
	string s="";
	if(str[0]=='\n') {s=s+str[1];s=s+str[2];}
	else s=str;
	for(int i=0;i<2;i++){
		((int)s[i]>57)?ret+=(s[i]-'a'+10)*pow(16,1-i):ret+=(s[i]-'0')*pow(16,1-i);
	}
	return ret;
}

inline void fill_sbox(){
	std::ifstream infile("AES_sbox");
	int i=0,j=0;
	string line="";
	while(std::getline(infile,line,'	')){
		s_box[i][j]=hextodec(line);
		j++;
		if(j>15){j=0;i++;}
		if(i==16) break;
	}
	/* forr(i,0,16){forr(j,0,16) cout<<s_box[i][j]<<" ";cout<<"\n";} */
}


inline void  initialize(){
	fill_sbox();
}



vector<vector<int>> addroundkey(vector<vector<int>> &input,vector<vector<int>> &key){
	vector<vector<int>> matrix=input;
	mt19937 mt(time(nullptr));
	for(int i=0;i<4;i++){
		for(int j=0;j<4;j++){
			int ran=mt();

			dbg(ran);

			//srfg part random operation on variable length
			/* matrix[i][j]=input[i][j]^key[i][j]; */
			if(ran%4==0)	matrix[i][j]=input[i][j]^key[i][j];
			else if(ran%4==1) matrix[i][j]=input[i][j]&key[i][j];
			else if(ran%4==2) matrix[i][j]=input[i][j]|key[i][j];
			else matrix[i][j]=!(input[i][j]^key[i][j]);
		}
	}
	return matrix;
}

inline int get_s_box_val(int a){
	int row=0,col=0;
	for(int i=0;i<8;i++){
		int val=(int)pow(2,i);
		if(val&a){
				(i>3)?row+=(int)pow(2,i-4):col+=(int)pow(2,i);
		}
	}
	return s_box[row][col];
}

vector<vector<int>> substitute_matrix(vector<vector<int>> &input){
	vector<vector<int>> matrix=input;
	for(int i=0;i<4;i++){
		for(int j=0;j<4;j++){
			matrix[i][j]=get_s_box_val(input[i][j]);
		}
	}
	return matrix;
}

inline vector<vector<int>> shift_rows(vector<vector<int>> &input){
	vector<vector<int>> matrix=input;
	for(int i=0;i<4;i++){
		queue<int> q;
		for(int j=0;j<i;j++) q.push(input[i][j]);
		int c=0;
		for(int j=i;j<4;j++){
			matrix[i][c]=input[i][j];
			c++;
		}
		while(!q.empty()){
			matrix[i][c]=q.front();
			q.pop();c++;
		}
	}
	return matrix;
}

vector<vector<int>> mix_columns(vector<vector<int>> &input){
	vector<vector<int>> matrix=input;
	vector<int> mul{2,3,1,1,};
	//right shift by 1 unit
	for(int i=0;i<4;i++){
		vector<int> v;
		stack<int> st;
		for(int j=0;j<i;j++) st.push(mul[3-j]);
		while(!st.empty()) {v.eb(st.top());st.pop();}
		for(int j=0;j<4-i;j++) v.eb(mul[j]);

		for(int j=0;j<4;j++){
			matrix[j][i]+=v[j]*matrix[j][i];
		}
	}
	return matrix;
}

vector<vector<int>> transpose(vector<vector<int>> &v){
	int n=v.size();
	int m=v[0].size();
	vector<vector<int>> temp=v;
	for(int i=0;i<n;i++){
		for(int j=0;j<m;j++){
			temp[j][i]=v[i][j];
		}
	}
	return temp;
}

inline vector<int>generate(vector<int> &word){
	vector<int> v;
	//left shift
	for(int i=1;i<word.size();i++) v.eb(word[i]);
	v.eb(word[0]);

	for(int i=0;i<v.size();i++) v[i]=get_s_box_val(v[i]);
	v[0]=v[0]^round_constant[rounds];
	rounds++;
	return v;
}


inline vector<vector<int>> key_expansion(vector<vector<int>> &prev_key){
	vector<vector<int>> next_keyt=prev_key;
	vector<vector<int>>  prev_keyt=transpose(prev_key);
	for(int i=0;i<4;i++){
		if(i==0){
			vector<int> temp=generate(prev_keyt[3]);
			for(int j=0;j<4;j++){
				next_keyt[i][j]=prev_keyt[i][j]^temp[j];
			}
		}
		else{
			for(int j=0;j<4;j++){
				next_keyt[i][j]=prev_keyt[i][j]^next_keyt[i-1][j];
			}
		}
	}
	return transpose(next_keyt);
}



int main()
{
    ios_base::sync_with_stdio(false);cin.tie(NULL);

	string input_text; 
	cin>>input_text; 
 	string input_key;
 	cin>>input_key;

 	vector<int> plain_text,key;  	
	for(int i=0;i<input_text.size();i++){ 
 		plain_text.eb((int)input_text[i]); 
 	} 
 	for(int i=0;i<input_key.size();i++){ 
 		key.eb((int)input_key[i]); 
	} 
	
	vector<vector<int>> state_matrix,key_state;
	state_matrix=key_state=vector<vector<int>>(4,vector<int> (4,0)); 
	int c=0;
	forr(i,0,4){
		forr(j,0,4){
			state_matrix[i][j]=plain_text[c];c++;
		}
	}
	c=0;
	forr(i,0,4){
		forr(j,0,4){
			key_state[i][j]=key[c];c++;
		}
	}

	initialize();	//fills s_box
	state_matrix=addroundkey(state_matrix,key_state);
	for(int i=0;i<9;i++){
		state_matrix=substitute_matrix(state_matrix);
		state_matrix=shift_rows(state_matrix);
		state_matrix=mix_columns(state_matrix);
		key_state=key_expansion(key_state);
		state_matrix=addroundkey(state_matrix,key_state);
	}
	state_matrix=substitute_matrix(state_matrix);
	state_matrix=shift_rows(state_matrix);
	key_state=key_expansion(key_state);
	state_matrix=addroundkey(state_matrix,key_state);
	vector<int> state_linear;
	for(int i=0;i<4;i++){for(int j=0;j<4;j++){state_linear.eb(state_matrix[i][j]);}}
	dbg(state_linear.size());
	for(int i=0;i<state_linear.size();i++) cout<<state_linear[i]<<" ";
	string final_cipher=dectohex(state_linear);
	dbg(final_cipher.size());
	cout<<final_cipher<<"\n";

    return 0;
}

