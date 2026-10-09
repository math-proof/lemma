#include "utility.h"

//extern "C" qword sum8args(qword rcx, qword rdx, qword r8, qword r9,
//		qword fifthArg, qword sixthArg, qword seventhArg, qword eighthArg);
//
//extern "C" double relu(double x);
//
//extern "C" double gelu(double x);
//
//extern "C" void stosd(void *edi, dword eax, qword rcx);
//extern "C" void *movsq(void *edi, const void *esi, qword rcx);
//
//extern "C" long long gcd_long(long long rcx, long long rdx);
//extern "C" qword gcd_qword(qword rcx, qword rdx);
//
//extern "C" int gcd_int(int rcx, int rdx);
//extern "C" dword gcd_dword(dword rcx, dword rdx);
//
//extern "C" double hard_sigmoid(double x);
//
//extern "C" double CalcSum_(float a, double b, float c, double d, float e,
//		double f);
//
//extern "C" double CalcDist_(int x1, double x2, long long y1, double y2,
//		float z1, short z2);
//
//double zero;
//extern "C" double one;
//extern "C" double half;

extern "C" {
qword sum8args(qword rcx, qword rdx, qword r8, qword r9, qword fifthArg,
		qword sixthArg, qword seventhArg, qword eighthArg);

double relu(double x);

double gelu(double x);

dword bsr_dword(dword rdi);
void stosb(void *rdi, BYTE al, qword rcx);
void stosw(void *rdi, word ax, qword rcx);
void stosd(void *rdi, dword eax, qword rcx);
void stosq(void *rdi, qword rax, qword rcx);

void stosq_double(void *rdi, double rax, qword rcx);

//find first of
void *scasb(const void *rdi, BYTE eax, qword rcx);
void *scasw(const void *rdi, word eax, qword rcx);
void *scasd(const void *rdi, dword eax, qword rcx);
void *scasq(const void *rdi, qword eax, qword rcx);

//find first not of
void *repe_scasd(const void *rdi, dword eax, qword rcx);

void* movsq(void *rdi, const void *esi, qword rcx);

void* movsd(void *rdi, const void *esi, qword rcx);

long long gcd_long(long long rcx, long long rdx);
qword gcd_qword(qword rcx, qword rdx);

int gcd_int(int rcx, int rdx);
dword gcd_dword(dword rcx, dword rdx);

double hard_sigmoid(double x);

double CalcSum_(float a, double b, float c, double d, float e, double f);

double CalcDist_(int x1, double x2, long long y1, double y2, float z1,
		short z2);

extern double zero;
extern double one;
extern double one_fifth;
extern double half;
}
