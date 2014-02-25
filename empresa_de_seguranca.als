module empresaDeSeguranca

sig sistema{
	bairros: set bairro
}

sig bairro{
	casas: set casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

// Fato sobre bairro
fact nomeBairro {
	one sistema
	all s: sistema | #s.bairros = 2
	one autoBranco
	one centro
	bairro = autoBranco + centro
}

sig casa{
	servicos: lone cercaEletrica
}

abstract sig servico{}

sig cercaEletrica extends servico{}

sig rondaNoturna extends servico{}

sig monitoramentoCameras extends servico{}

pred show[]{}
run show for 3
