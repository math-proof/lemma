<template>
	<button type=button class=transparent @click=click :title="show? 'click to collapse' : 'click to expand'">{{buttonText}}<br></button>
</template>

<script>
// console.log('import buttonExpand.vue');

export default {
	props : [ 'initial_show', 'callback'],

    data() {
        return {
			show: this.initial_show,
        };
    },

    computed: {

		buttonText() {
			return this.show? '«««' : '»»»';
		},
    },

    created() {
    },

    methods: {
		click(event) {
			this.show = !this.show;

			if (this.callback)
				this.callback();
		},
    },

	directives: {
	},

}
</script>

<style>

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
}

button.transparent:hover{
	background-color: red;
}

</style>
