module empresaDeSeguranca

sig bairro{
	casas: set casa
}

one sig autoBranco extends bairro{}

one sig centro extends bairro{}

// Fato sobre bairro
fact nomeBairro {
	all b: bairro | some b.casas
	bairro = autoBranco && centro
}

sig casa{}

fact sobreCasa{
	all c:casa | some c.servico
}

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
