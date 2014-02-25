module empresaDeSeguranca

sig bairro{
	casas: set casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

// Fato sobre bairro
fact nomeBairro {
	all b: bairro | some b.casas
	bairro = autoBranco + centro
}

sig casa{}

abstract sig servico{}

sig cercaEletrica extends servico{}

sig rondaNoturna extends servico{
	r: one cercaEletrica
}

sig monitoramentoCameras extends servico{
	r: one cercaEletrica
}

pred show[]{}
run show for 3
